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
def X0Split32A0X0Y0Certs : List (Nat × Nat) := [
  (106, 391), (172, 642), (1084, 805), (1150, 1112), (1541, 905),
  (1610, 1244), (2647, 160), (2649, 164), (3380, 1381), (3433, 1683),
  (3557, 293), (3842, 1531), (5329, 397), (5332, 408), (5780, 461),
  (5783, 468), (6260, 628), (6513, 1880), (8049, 818), (8053, 835),
  (8506, 919), (8510, 942), (8953, 1001), (8964, 1027), (10781, 1406),
  (10785, 1439), (11228, 1509), (11243, 1566), (12592, 1843), (12609, 1934)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0X0Y0_check. -/
theorem X0Split32A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split32A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0X0Y0_pairs. -/
theorem X0Split32A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split32A0X0Y0Certs
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
  · exact X0Split32A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0X0_pairs. -/
theorem X0Split32A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split32A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split32A0_pairs. -/
theorem X0Split32A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split32A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split32_check. -/
theorem X0Split32_check : checkSplit m4TX0 (1, 3, 2, 0) = true := by
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
    · exact X0Split32A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split33A0X0Y0Certs : List (Nat × Nat) := [
  (59, 1816), (131, 215), (171, 785), (287, 497), (301, 10),
  (356, 1351), (473, 993), (484, 53), (515, 72), (657, 1497),
  (669, 153), (700, 192), (795, 386), (826, 453), (892, 894)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0X0Y0_check. -/
theorem X0Split33A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split33A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0X0Y0_pairs. -/
theorem X0Split33A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split33A0X0Y0Certs
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
  · exact X0Split33A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0X0_pairs. -/
theorem X0Split33A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split33A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split33A0_pairs. -/
theorem X0Split33A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split33A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split33_check. -/
theorem X0Split33_check : checkSplit m4TX0 (1, 4, 1, 0) = true := by
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
    · exact X0Split33A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split34A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0X0Y0_check. -/
theorem X0Split34A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split34A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0X0Y0_pairs. -/
theorem X0Split34A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 5
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split34A0X0Y0Certs
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
  · exact X0Split34A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0X0_pairs. -/
theorem X0Split34A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split34A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split34A0_pairs. -/
theorem X0Split34A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 5 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split34A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split34_check. -/
theorem X0Split34_check : checkSplit m4TX0 (1, 5, 0, 0) = true := by
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
    · exact X0Split34A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split35A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0X0Y0_check. -/
theorem X0Split35A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split35A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0X0Y0_pairs. -/
theorem X0Split35A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split35A0X0Y0Certs
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
  · exact X0Split35A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0X0_pairs. -/
theorem X0Split35A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split35A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split35A0_pairs. -/
theorem X0Split35A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 4 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split35A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split35_check. -/
theorem X0Split35_check : checkSplit m4TX0 (2, 0, 4, 1) = true := by
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
    · exact X0Split35A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split36A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0X0Y0_check. -/
theorem X0Split36A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split36A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0X0Y0_pairs. -/
theorem X0Split36A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split36A0X0Y0Certs
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
  · exact X0Split36A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0X0_pairs. -/
theorem X0Split36A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split36A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split36A0_pairs. -/
theorem X0Split36A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split36A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split36_check. -/
theorem X0Split36_check : checkSplit m4TX0 (2, 1, 3, 1) = true := by
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
    · exact X0Split36A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split37A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X0Y0_check. -/
theorem X0Split37A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X0Y0_pairs. -/
theorem X0Split37A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 2
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X0Y0Certs
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
  · exact X0Split37A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X0_pairs. -/
theorem X0Split37A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split37A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split37A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X1Y0_check. -/
theorem X0Split37A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X1Y0_pairs. -/
theorem X0Split37A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 2
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split37A0X1Y0Certs
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
  · exact X0Split37A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0X1_pairs. -/
theorem X0Split37A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split37A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37A0_pairs. -/
theorem X0Split37A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 2 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split37A0X0_pairs x hx y hy hw
  · exact X0Split37A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split37_check. -/
theorem X0Split37_check : checkSplit m4TX0 (2, 2, 2, 0) = true := by
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
    · exact X0Split37A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split38A0X0Y0Certs : List (Nat × Nat) := [
  (228, 557), (463, 297), (972, 255), (1200, 0), (1369, 634),
  (1524, 1093), (1983, 39), (2059, 633), (2450, 721), (3018, 560),
  (3422, 22), (3684, 1099), (3903, 33), (4195, 1229), (4438, 1651),
  (4657, 107), (4753, 298), (4794, 1098), (5228, 134), (5365, 1226),
  (5946, 90), (6150, 2), (6342, 258), (6756, 89), (7113, 36),
  (7417, 111), (7828, 1656), (8108, 129), (8504, 343), (8630, 718),
  (8698, 1654), (9240, 6), (9432, 257), (9632, 21), (9919, 635),
  (10117, 110), (10423, 301), (10928, 136), (11234, 342), (11376, 85),
  (11762, 24), (11958, 563), (12535, 1227), (12764, 347), (13010, 719)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0X0Y0_check. -/
theorem X0Split38A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split38A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0X0Y0_pairs. -/
theorem X0Split38A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split38A0X0Y0Certs
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
  · exact X0Split38A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0X0_pairs. -/
theorem X0Split38A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split38A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split38A0_pairs. -/
theorem X0Split38A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split38A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split38_check. -/
theorem X0Split38_check : checkSplit m4TX0 (2, 3, 1, 0) = true := by
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
    · exact X0Split38A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split39A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0X0Y0_check. -/
theorem X0Split39A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split39A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0X0Y0_pairs. -/
theorem X0Split39A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split39A0X0Y0Certs
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
  · exact X0Split39A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0X0_pairs. -/
theorem X0Split39A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split39A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split39A0_pairs. -/
theorem X0Split39A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 4 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split39A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split39_check. -/
theorem X0Split39_check : checkSplit m4TX0 (2, 4, 0, 0) = true := by
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
    · exact X0Split39A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split40A0X0Y0Certs : List (Nat × Nat) := [
  (241, 1684), (501, 1837), (834, 1341), (896, 471), (984, 947),
  (1063, 629), (1214, 412), (1371, 1606), (1454, 244), (1577, 542),
  (1681, 814), (1887, 1332)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X0Y0_check. -/
theorem X0Split40A0X0Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split40A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X0Y0_pairs. -/
theorem X0Split40A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split40A0X0Y0Certs
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
  · exact X0Split40A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X0_pairs. -/
theorem X0Split40A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split40A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split40A0X1Y0Certs : List (Nat × Nat) := [
  (68, 1445), (86, 1695), (197, 1045), (306, 1113), (357, 1597),
  (443, 841), (685, 1075), (707, 1400), (839, 331), (960, 1395),
  (1026, 697), (1128, 1807), (1349, 167), (1430, 1968), (1442, 708),
  (1775, 773), (1871, 1208), (1884, 1922)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X1Y0_check. -/
theorem X0Split40A0X1Y0_check : checkGrid m4TX0 censusX0 1 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split40A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X1Y0_pairs. -/
theorem X0Split40A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 1 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M1LeftColumns X0M1RightColumns) X0Split40A0X1Y0Certs
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
  · exact X0Split40A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0X1_pairs. -/
theorem X0Split40A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split40A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40A0_pairs. -/
theorem X0Split40A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 1 x y 0) = 3 →
      sweepAccept m4TX0 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split40A0X0_pairs x hx y hy hw
  · exact X0Split40A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split40_check. -/
theorem X0Split40_check : checkSplit m4TX0 (3, 0, 3, 1) = true := by
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
    · exact X0Split40A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A0X0Y0Certs : List (Nat × Nat) := [
  (901, 0), (4910, 0), (12115, 0), (12127, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0X0Y0_check. -/
theorem X0Split41A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0X0Y0_pairs. -/
theorem X0Split41A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split41A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0X0_pairs. -/
theorem X0Split41A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A0_pairs. -/
theorem X0Split41A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1X0Y0_check. -/
theorem X0Split41A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1X0Y0_pairs. -/
theorem X0Split41A1X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split41A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1X0_pairs. -/
theorem X0Split41A1X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A1_pairs. -/
theorem X0Split41A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2X0Y0_check. -/
theorem X0Split41A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2X0Y0_pairs. -/
theorem X0Split41A2X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split41A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2X0_pairs. -/
theorem X0Split41A2X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A2_pairs. -/
theorem X0Split41A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split41A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3X0Y0_check. -/
theorem X0Split41A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3X0Y0_pairs. -/
theorem X0Split41A3X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 3
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split41A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split41A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3X0_pairs. -/
theorem X0Split41A3X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split41A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41A3_pairs. -/
theorem X0Split41A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split41A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split41_check. -/
theorem X0Split41_check : checkSplit m4TX0 (3, 1, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split41A0_pairs x hx y hy hw
    · exact X0Split41A1_pairs x hx y hy hw
    · exact X0Split41A2_pairs x hx y hy hw
    · exact X0Split41A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A0X0Y0Certs : List (Nat × Nat) := [
  (7536, 0), (8457, 0), (9080, 0), (10891, 0), (12265, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0X0Y0_check. -/
theorem X0Split42A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0X0Y0_pairs. -/
theorem X0Split42A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0X0_pairs. -/
theorem X0Split42A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A0_pairs. -/
theorem X0Split42A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 3 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1X0Y0_check. -/
theorem X0Split42A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1X0Y0_pairs. -/
theorem X0Split42A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1X0_pairs. -/
theorem X0Split42A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A1_pairs. -/
theorem X0Split42A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 3 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2X0Y0_check. -/
theorem X0Split42A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2X0Y0_pairs. -/
theorem X0Split42A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2X0_pairs. -/
theorem X0Split42A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A2_pairs. -/
theorem X0Split42A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 3 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split42A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3X0Y0_check. -/
theorem X0Split42A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3X0Y0_pairs. -/
theorem X0Split42A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 3
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split42A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks1S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X0Split42A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3X0_pairs. -/
theorem X0Split42A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split42A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42A3_pairs. -/
theorem X0Split42A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 3 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split42A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split42_check. -/
theorem X0Split42_check : checkSplit m4TX0 (3, 2, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split42A0_pairs x hx y hy hw
    · exact X0Split42A1_pairs x hx y hy hw
    · exact X0Split42A2_pairs x hx y hy hw
    · exact X0Split42A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split43A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X0Y0_check. -/
theorem X0Split43A0X0Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split43A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X0Y0_pairs. -/
theorem X0Split43A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split43A0X0Y0Certs
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
  · exact X0Split43A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X0_pairs. -/
theorem X0Split43A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split43A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split43A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X1Y0_check. -/
theorem X0Split43A0X1Y0_check : checkGrid m4TX0 censusX0 0 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split43A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X1Y0_pairs. -/
theorem X0Split43A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 0 0 3
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X0M0LeftColumns X0M0RightColumns) X0Split43A0X1Y0Certs
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
  · exact X0Split43A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0X1_pairs. -/
theorem X0Split43A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split43A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43A0_pairs. -/
theorem X0Split43A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 0 x y 0) = 3 →
      sweepAccept m4TX0 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X0Split43A0X0_pairs x hx y hy hw
  · exact X0Split43A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split43_check. -/
theorem X0Split43_check : checkSplit m4TX0 (3, 3, 0, 0) = true := by
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
    · exact X0Split43A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A0X0Y0Certs : List (Nat × Nat) := [
  (167, 0), (226, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0X0Y0_check. -/
theorem X0Split44A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0X0Y0_pairs. -/
theorem X0Split44A0X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split44A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0X0_pairs. -/
theorem X0Split44A0X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A0_pairs. -/
theorem X0Split44A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1X0Y0_check. -/
theorem X0Split44A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1X0Y0_pairs. -/
theorem X0Split44A1X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split44A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1X0_pairs. -/
theorem X0Split44A1X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A1_pairs. -/
theorem X0Split44A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2X0Y0_check. -/
theorem X0Split44A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2X0Y0_pairs. -/
theorem X0Split44A2X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split44A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2X0_pairs. -/
theorem X0Split44A2X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A2_pairs. -/
theorem X0Split44A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split44A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3X0Y0_check. -/
theorem X0Split44A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3X0Y0_pairs. -/
theorem X0Split44A3X0Y0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 4
    outerMasks0S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split44A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S256Chunk0 masks2S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S256Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X0Split44A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3X0_pairs. -/
theorem X0Split44A3X0_pairs : ∀ x ∈ outerMasks0S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split44A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44A3_pairs. -/
theorem X0Split44A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split44A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split44_check. -/
theorem X0Split44_check : checkSplit m4TX0 (4, 0, 2, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split44A0_pairs x hx y hy hw
    · exact X0Split44A1_pairs x hx y hy hw
    · exact X0Split44A2_pairs x hx y hy hw
    · exact X0Split44A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0X0Y0_check. -/
theorem X0Split45A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0X0Y0_pairs. -/
theorem X0Split45A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split45A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0X0_pairs. -/
theorem X0Split45A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A0_pairs. -/
theorem X0Split45A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1X0Y0_check. -/
theorem X0Split45A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1X0Y0_pairs. -/
theorem X0Split45A1X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split45A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1X0_pairs. -/
theorem X0Split45A1X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A1_pairs. -/
theorem X0Split45A1_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A2X0Y0Certs : List (Nat × Nat) := [
  (740, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2X0Y0_check. -/
theorem X0Split45A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2X0Y0_pairs. -/
theorem X0Split45A2X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split45A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2X0_pairs. -/
theorem X0Split45A2X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A2_pairs. -/
theorem X0Split45A2_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split45A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3X0Y0_check. -/
theorem X0Split45A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3X0Y0_pairs. -/
theorem X0Split45A3X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 4
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split45A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split45A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3X0_pairs. -/
theorem X0Split45A3X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split45A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45A3_pairs. -/
theorem X0Split45A3_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split45A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split45_check. -/
theorem X0Split45_check : checkSplit m4TX0 (4, 1, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split45A0_pairs x hx y hy hw
    · exact X0Split45A1_pairs x hx y hy hw
    · exact X0Split45A2_pairs x hx y hy hw
    · exact X0Split45A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0X0Y0_check. -/
theorem X0Split46A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0X0Y0_pairs. -/
theorem X0Split46A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0X0_pairs. -/
theorem X0Split46A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A0_pairs. -/
theorem X0Split46A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 4 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1X0Y0_check. -/
theorem X0Split46A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1X0Y0_pairs. -/
theorem X0Split46A1X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1X0_pairs. -/
theorem X0Split46A1X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A1_pairs. -/
theorem X0Split46A1_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 4 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A2X0Y0Certs : List (Nat × Nat) := [
  (25, 0)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2X0Y0_check. -/
theorem X0Split46A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2X0Y0_pairs. -/
theorem X0Split46A2X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2X0_pairs. -/
theorem X0Split46A2X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A2_pairs. -/
theorem X0Split46A2_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 4 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split46A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3X0Y0_check. -/
theorem X0Split46A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3X0Y0_pairs. -/
theorem X0Split46A3X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 4
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split46A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks2S2048Chunk0 masks0S512Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X0Split46A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3X0_pairs. -/
theorem X0Split46A3X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split46A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46A3_pairs. -/
theorem X0Split46A3_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 4 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split46A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split46_check. -/
theorem X0Split46_check : checkSplit m4TX0 (4, 2, 0, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split46A0_pairs x hx y hy hw
    · exact X0Split46A1_pairs x hx y hy hw
    · exact X0Split46A2_pairs x hx y hy hw
    · exact X0Split46A3_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0X0Y0_check. -/
theorem X0Split47A0X0Y0_check : checkGrid m4TX0 censusX0 2 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0X0Y0_pairs. -/
theorem X0Split47A0X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 0 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A0X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split47A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0X0_pairs. -/
theorem X0Split47A0X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A0_pairs. -/
theorem X0Split47A0_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 0) = 5 →
      sweepAccept m4TX0 2 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A1X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1X0Y0_check. -/
theorem X0Split47A1X0Y0_check : checkGrid m4TX0 censusX0 2 91076351 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A1X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1X0Y0_pairs. -/
theorem X0Split47A1X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 91076351 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A1X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split47A1X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1X0_pairs. -/
theorem X0Split47A1X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A1X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A1_pairs. -/
theorem X0Split47A1_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 91076351) = 5 →
      sweepAccept m4TX0 2 x y 91076351 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A1X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A2X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2X0Y0_check. -/
theorem X0Split47A2X0Y0_check : checkGrid m4TX0 censusX0 2 985062231 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A2X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2X0Y0_pairs. -/
theorem X0Split47A2X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 985062231 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A2X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split47A2X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2X0_pairs. -/
theorem X0Split47A2X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A2X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A2_pairs. -/
theorem X0Split47A2_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 985062231) = 5 →
      sweepAccept m4TX0 2 x y 985062231 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A2X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X0Split47A3X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3X0Y0_check. -/
theorem X0Split47A3X0Y0_check : checkGrid m4TX0 censusX0 2 1071345064 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A3X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3X0Y0_pairs. -/
theorem X0Split47A3X0Y0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  apply checkGrid_sound m4TX0 censusX0 2 1071345064 5
    outerMasks0S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns) X0Split47A3X0Y0Certs
  · exact censusX0_valid
  · decide
  · decide
  · decide
  · exact outerMasks0S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
  · intro y hy
    exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX0 2 outerMasks0S2048Chunk0 masks1S2048Chunk0
      X0M2LeftColumns X0M2RightColumns
    · decide
    · exact outerMasks0S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X0M2Left_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X0M2Right_columns_bound z hz).1,
        lt_of_lt_of_le (X0M2Right_columns_bound z hz).2 (by decide)⟩
    · exact X0M2Left_eq
    · exact X0M2Right_eq
    · intro x hx
      exact X0M2Left_bound x (outerMasks0S2048Chunk0_bound x hx)
    · intro y hy
      exact X0M2Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X0Split47A3X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3X0_pairs. -/
theorem X0Split47A3X0_pairs : ∀ x ∈ outerMasks0S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X0Split47A3X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47A3_pairs. -/
theorem X0Split47A3_pairs : ∀ x ∈ masksOfWt 30 0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX0 2 x y 1071345064) = 5 →
      sweepAccept m4TX0 2 x y 1071345064 = true := by
  intro x hx y hy hw
  rw [← outerMasks0S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X0Split47A3X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0Split47_check. -/
theorem X0Split47_check : checkSplit m4TX0 (5, 0, 1, 2) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X0M2Left_bound x (masksOfWt_bound 30 0 x hx)
    · exact X0M2Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X0M2_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0, 91076351, 985062231, 1071345064
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl | rfl | rfl | rfl
    · exact X0Split47A0_pairs x hx y hy hw
    · exact X0Split47A1_pairs x hx y hy hw
    · exact X0Split47A2_pairs x hx y hy hw
    · exact X0Split47A3_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

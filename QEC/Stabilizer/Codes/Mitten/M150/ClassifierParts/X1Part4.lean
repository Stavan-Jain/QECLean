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
def X1Split64A0X0Y0Certs : List (Nat × Nat) := [
  (55, 308), (165, 886), (270, 1668), (429, 3369), (460, 150),
  (461, 156), (468, 182), (535, 521), (553, 606), (565, 672),
  (615, 998), (749, 2092), (816, 2868), (1008, 742), (1023, 841),
  (1232, 2624), (1244, 2768), (1775, 188), (1827, 454), (1828, 465),
  (1841, 528), (1945, 1181), (1969, 1346), (1987, 1475), (2031, 1852),
  (2138, 2996), (2611, 37), (2869, 1593), (3033, 3260), (3043, 3443),
  (3484, 53), (3528, 258), (3565, 443), (3581, 531), (3589, 573),
  (3674, 1117), (3695, 1265), (3731, 1529), (3796, 2103), (4019, 545),
  (4101, 1045), (4102, 1063), (4121, 1197), (4128, 1257), (4192, 1779),
  (4223, 2059), (4236, 2162), (4262, 2454), (4802, 115), (4840, 306),
  (4944, 858), (5218, 3441), (5237, 116), (5484, 1616), (5583, 2634),
  (5637, 3210), (6115, 149), (6136, 251), (6217, 659), (6274, 1025),
  (6296, 1199), (6309, 1283), (6399, 2064), (6440, 2545), (6490, 3017),
  (6534, 76), (6547, 142), (6734, 1223), (6822, 1942), (6823, 1971),
  (6847, 2192), (6855, 2281), (6904, 2864), (6917, 2929), (7461, 363),
  (7467, 376), (7533, 739), (7812, 3211), (7902, 378), (7977, 774),
  (8198, 2678), (8254, 3288), (8787, 453), (8806, 568), (8824, 650),
  (8944, 1447), (8995, 1903), (9022, 2190), (9033, 2296), (9083, 2881),
  (9093, 2943), (9139, 52), (9167, 179), (9178, 225), (9185, 264),
  (9217, 432), (9333, 1130), (9459, 2230), (9463, 2275), (9539, 3108),
  (10152, 775), (10160, 849), (10170, 885), (10264, 1589), (10928, 281),
  (10971, 501), (11061, 1048), (11089, 1261), (11093, 1273), (11115, 1428),
  (11154, 1786), (11219, 2395), (11279, 3107), (11760, 113), (11898, 842),
  (12015, 1666), (12108, 2630), (12204, 147), (12213, 183), (12217, 208),
  (12272, 493), (12314, 703), (12380, 1139), (12461, 1793), (12477, 1944),
  (12520, 2361), (12616, 35), (12683, 369), (12989, 2766), (13039, 3287)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0X0Y0_check. -/
theorem X1Split64A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split64A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0X0Y0_pairs. -/
theorem X1Split64A0X0Y0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masks2S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks1S256Chunk0 masks2S2048Chunk0
    (gridWords outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split64A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S256Chunk0_bound
  · exact masks2S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S256Chunk0 masks2S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S256Chunk0_bound
    · exact masks2S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S2048Chunk0_bound y hy)
  · exact X1Split64A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0X0_pairs. -/
theorem X1Split64A0X0_pairs : ∀ x ∈ outerMasks1S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split64A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split64A0_pairs. -/
theorem X1Split64A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split64A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split64_check. -/
theorem X1Split64_check : checkSplit m4TX1 (1, 5, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split64A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split65A0X0Y0Certs : List (Nat × Nat) := [
  (2, 32), (17, 734), (27, 2578), (39, 201), (43, 418),
  (66, 100), (83, 1562), (89, 3160), (135, 563), (139, 963),
  (191, 297), (192, 357), (207, 2571), (256, 640), (260, 1105),
  (291, 1243), (294, 1770), (332, 34), (342, 361), (347, 729),
  (377, 730), (378, 838), (389, 3165), (442, 1398), (445, 2033),
  (451, 18), (453, 43), (516, 98), (528, 839), (533, 1563),
  (540, 9), (551, 303), (563, 1571), (626, 2262), (628, 2858),
  (634, 66), (637, 131), (690, 10), (702, 353), (717, 2576),
  (755, 88), (758, 162), (812, 25), (828, 833), (839, 3170),
  (850, 247), (854, 486), (870, 8), (876, 104), (881, 301)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0X0Y0_check. -/
theorem X1Split65A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split65A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0X0Y0_pairs. -/
theorem X1Split65A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks1S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 6
    outerMasks1S2048Chunk0 masks1S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split65A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks1S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S2048Chunk0 masks1S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks1S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S2048Chunk0_bound y hy)
  · exact X1Split65A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0X0_pairs. -/
theorem X1Split65A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split65A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split65A0_pairs. -/
theorem X1Split65A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split65A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split65_check. -/
theorem X1Split65_check : checkSplit m4TX1 (1, 6, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split65A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split66A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0X0Y0_check. -/
theorem X1Split66A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split66A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0X0Y0_pairs. -/
theorem X1Split66A0X0Y0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masks0S2048Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 7
    outerMasks1S2048Chunk0 masks0S2048Chunk0
    (gridWords outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split66A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks1S2048Chunk0_bound
  · exact masks0S2048Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks1S2048Chunk0 masks0S2048Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks1S2048Chunk0_bound
    · exact masks0S2048Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks1S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S2048Chunk0_bound y hy)
  · exact X1Split66A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0X0_pairs. -/
theorem X1Split66A0X0_pairs : ∀ x ∈ outerMasks1S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S2048_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split66A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split66A0_pairs. -/
theorem X1Split66A0_pairs : ∀ x ∈ masksOfWt 30 1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 7 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks1S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks1S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split66A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split66_check. -/
theorem X1Split66_check : checkSplit m4TX1 (1, 7, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 1 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split66A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split67A0X0Y0Certs : List (Nat × Nat) := [
  (39, 3418), (112, 1726), (172, 3503), (195, 2847), (223, 2796),
  (239, 2734), (280, 3489), (310, 3269), (339, 3410), (394, 1642)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0X0Y0_check. -/
theorem X1Split67A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split67A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0X0Y0_pairs. -/
theorem X1Split67A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split67A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split67A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0X0_pairs. -/
theorem X1Split67A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split67A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split67A0_pairs. -/
theorem X1Split67A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 6 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split67A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split67_check. -/
theorem X1Split67_check : checkSplit m4TX1 (2, 0, 6, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split67A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split68A0X0Y0Certs : List (Nat × Nat) := [
  (229, 1387), (236, 1495), (985, 2562), (1126, 2160), (1172, 2827),
  (1176, 2826), (1193, 1900), (1199, 3416), (1205, 2487), (1224, 2252),
  (1327, 2001), (2775, 1916), (2992, 3101), (2994, 1079), (3028, 3127),
  (3185, 619), (3292, 3105), (3366, 3495), (3371, 801), (3372, 3295),
  (3387, 1676), (3416, 3031), (3423, 3048), (3430, 2530), (3583, 2463),
  (5160, 806), (5171, 3483), (5178, 3283), (5183, 2812), (5740, 2413),
  (5841, 1968), (5856, 3437), (5867, 2321), (5868, 2507), (5873, 3517),
  (5953, 1502), (6123, 2010), (6146, 3138), (6158, 1054), (6343, 629),
  (6352, 1332), (6430, 1372), (6549, 1034), (6596, 3052), (6702, 3457),
  (6707, 1729), (6708, 333), (6719, 2786), (6725, 2467), (6757, 237),
  (6766, 1858), (6919, 2369), (7170, 3405), (7176, 3258), (7181, 2804),
  (7199, 2727), (8400, 1736), (8402, 1735), (8417, 3326), (8427, 3488),
  (9054, 1354), (9136, 1938), (9243, 2072), (9271, 2199), (9300, 2773),
  (9312, 1624), (9323, 950), (9327, 3320), (9439, 2498), (9605, 2442),
  (9607, 2541), (9644, 1960), (10172, 2765), (10181, 3354), (10182, 1514),
  (10187, 3511), (11390, 1542), (11463, 1922), (11596, 2157), (11599, 2928),
  (11632, 2241), (11767, 2961), (11794, 3125), (11822, 3451), (11838, 2696),
  (11847, 1716), (11849, 1684), (11964, 2449), (12100, 1178), (12103, 2547)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0X0Y0_check. -/
theorem X1Split68A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split68A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0X0Y0_pairs. -/
theorem X1Split68A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split68A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split68A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0X0_pairs. -/
theorem X1Split68A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split68A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split68A0_pairs. -/
theorem X1Split68A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split68A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split68_check. -/
theorem X1Split68_check : checkSplit m4TX1 (2, 1, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split68A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split69A0X0Y0Certs : List (Nat × Nat) := [
  (3069, 1494), (3133, 1374), (3337, 1964), (4465, 1088), (4479, 826),
  (4480, 2480), (7830, 2042), (8762, 1128), (8843, 2817), (10696, 3038),
  (12628, 2540), (12835, 1986), (12930, 3013), (13000, 2402), (14100, 1976),
  (14115, 2428), (14307, 3115), (16294, 1957), (16966, 3415), (17033, 3513),
  (17042, 1896), (17101, 2023), (17120, 1828), (17224, 3512), (17236, 2828),
  (17327, 3420), (17339, 1890), (17398, 3419), (17485, 2484), (17587, 2184),
  (17634, 2124), (19222, 1839), (19387, 1930), (19445, 2131), (20671, 2025),
  (20691, 1764), (20692, 2508), (21770, 1312), (25315, 1920), (25433, 1164),
  (25537, 2196), (31763, 2886), (33209, 2088), (33326, 3515), (37333, 2615),
  (40059, 1813), (40250, 1954), (40271, 2411), (41377, 2514), (41411, 1819),
  (41446, 2351), (41724, 1519), (43115, 1075), (43192, 3087), (43403, 3133),
  (43613, 462), (43791, 2302), (43810, 2108), (46139, 2335), (47730, 1326),
  (48735, 758), (48737, 406), (48879, 3275), (48890, 382), (48975, 2682),
  (49071, 3448), (49083, 3219), (49137, 318), (49143, 2779), (49153, 1631),
  (49179, 3029), (49330, 2311), (49538, 3057), (49774, 2521), (49888, 3007),
  (49922, 3050), (51945, 1073), (52112, 2070), (52153, 3061), (55042, 2669),
  (55156, 2850), (55157, 2821), (56626, 1179), (62389, 1979), (62524, 2138),
  (62596, 3117), (72252, 394), (73787, 2991), (73885, 3526), (74502, 918),
  (74875, 1731), (74881, 805), (74967, 3241), (74975, 2802), (74979, 2723),
  (74985, 1646), (75090, 1647), (75173, 905), (75188, 3386), (75238, 2654),
  (79507, 3516), (79513, 2272), (80459, 3249), (83193, 1503), (83219, 2379),
  (83269, 2353), (84502, 612), (84691, 1201), (84740, 1932), (84882, 3434),
  (84891, 2390), (84897, 2503), (84972, 2506), (84990, 3438), (85084, 2393),
  (85176, 3440), (85193, 2392), (85237, 3436), (85248, 2386), (86329, 3144),
  (86594, 2522), (86698, 277), (86750, 682), (86800, 1159), (88870, 2005),
  (88916, 1468), (88984, 3082), (89388, 609), (89399, 1060), (89569, 3027),
  (91811, 621), (91966, 1057), (92064, 1878), (93185, 1053), (94949, 1051),
  (94964, 2466), (95110, 2400), (95664, 1418), (97071, 1683), (97073, 1636),
  (97077, 936), (97152, 763), (97258, 894), (97269, 3468), (97362, 3374),
  (97413, 3220), (97422, 2709), (97429, 802), (97493, 1436), (97525, 2462),
  (97725, 683), (97958, 460), (98170, 1012), (98203, 233), (100178, 1907),
  (100341, 1999), (100380, 2955), (100860, 1898), (100915, 1892), (103966, 2728),
  (103982, 2790), (104020, 3252), (104033, 921), (104113, 3387), (104218, 1662),
  (104334, 1665), (104388, 689), (104394, 3465), (104398, 2674), (105646, 3514),
  (105716, 3414), (106034, 3356), (106035, 3255), (107614, 2158)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X0Y0_check. -/
theorem X1Split69A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X0Y0_pairs. -/
theorem X1Split69A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split69A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X0_pairs. -/
theorem X1Split69A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split69A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split69A0X1Y0Certs : List (Nat × Nat) := [
  (1350, 782), (1352, 398), (2238, 817), (5834, 479), (5950, 2320),
  (6057, 3070), (11103, 1382), (11603, 2189), (11760, 3509), (11811, 3331),
  (11883, 2815), (11893, 1734), (11898, 2739), (11909, 3329), (12015, 1095),
  (12119, 2740), (12157, 1022), (12174, 2738), (17410, 127), (17558, 3215),
  (18452, 1376), (20930, 1351), (21093, 2441), (21125, 1843), (22402, 2499),
  (22436, 1536), (22480, 1195), (23954, 1937), (24583, 1359), (24742, 2200),
  (24743, 2110), (24872, 899), (24937, 407), (24948, 778), (24950, 383),
  (24960, 2687), (25059, 1672), (25065, 2683), (25158, 1702), (25203, 2780),
  (25224, 856), (26850, 2923), (27065, 1136), (27220, 700), (27266, 1501),
  (27304, 2133), (29392, 2526), (29431, 2443), (29489, 3010), (29602, 1353),
  (29771, 1967), (29819, 2419), (32248, 1690), (32599, 910), (33822, 2951),
  (37427, 3362), (37482, 3491), (37548, 1444), (37569, 1443), (37674, 1511),
  (37681, 2762), (37763, 2760), (37772, 3365), (37816, 2764), (37827, 3363),
  (39149, 3523), (39191, 2345), (39199, 348), (39200, 1492), (41121, 3078),
  (45797, 1692), (45801, 924), (47130, 1752), (50926, 2391), (51174, 906),
  (51185, 1097), (54892, 1919), (55114, 2195), (55149, 1997), (56137, 988),
  (56245, 1912), (56460, 1157), (57903, 2149), (58093, 2204), (58185, 2338),
  (58369, 2458), (58569, 2187), (58640, 2555), (60560, 2212), (60944, 3126),
  (60953, 3030), (61072, 1995), (61336, 1677), (61350, 896), (61396, 3469),
  (61488, 3384), (61505, 938), (61600, 939), (61697, 271), (61703, 2777),
  (61709, 3376), (61759, 2618), (63474, 1043), (63620, 3063), (63709, 2100),
  (63813, 2496), (63859, 1525), (65373, 1204), (65531, 1174), (65597, 1421),
  (72447, 2819), (72453, 1558), (73788, 2816), (77019, 1036), (77093, 512),
  (77188, 1934)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X1Y0_check. -/
theorem X1Split69A0X1Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X1Y0_pairs. -/
theorem X1Split69A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split69A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split69A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0X1_pairs. -/
theorem X1Split69A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split69A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69A0_pairs. -/
theorem X1Split69A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split69A0X0_pairs x hx y hy hw
  · exact X1Split69A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split69_check. -/
theorem X1Split69_check : checkSplit m4TX1 (2, 2, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split69A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y0Certs : List (Nat × Nat) := [
  (13359, 290), (14641, 195), (18601, 523), (26834, 550), (31671, 403),
  (35774, 413), (42270, 533), (45951, 555), (49726, 267), (51183, 372),
  (65148, 197), (78561, 442), (88429, 287), (90533, 549), (93671, 517),
  (99324, 268), (101653, 332), (101706, 386), (105051, 524)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y0_check. -/
theorem X1Split70A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y0_pairs. -/
theorem X1Split70A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X1Split70A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y1Certs : List (Nat × Nat) := [
  (3959, 822), (11638, 610), (13494, 664), (14454, 575), (16072, 696),
  (33371, 681), (34519, 721), (35885, 668), (36133, 589), (40662, 746),
  (43145, 693), (61833, 625), (62395, 803), (62401, 804), (69137, 694),
  (79213, 678), (80749, 762), (81013, 671), (81436, 715), (83061, 588),
  (86441, 685), (86452, 687), (86630, 823)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y1_check. -/
theorem X1Split70A0X0Y1_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y1_pairs. -/
theorem X1Split70A0X0Y1_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X1Split70A0X0Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y2Certs : List (Nat × Nat) := [
  (34545, 1008), (36306, 864), (36346, 876), (36778, 979), (51980, 932),
  (55808, 904), (56203, 954), (64430, 1069), (69572, 1028), (70904, 1056),
  (72275, 866), (72314, 880), (73084, 991)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y2_check. -/
theorem X1Split70A0X0Y2_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y2_pairs. -/
theorem X1Split70A0X0Y2_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y2Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X1Split70A0X0Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y3Certs : List (Nat × Nat) := [
  (2881, 1154), (3022, 1277), (4331, 1337), (11622, 1127), (12885, 1156),
  (17984, 1366), (40026, 1129), (40375, 1355), (45709, 1187), (45844, 1290),
  (47822, 1278), (52461, 1149), (57377, 1229), (77724, 1203), (77819, 1275),
  (81632, 1131), (82186, 1237), (82291, 1313), (87423, 1281), (87590, 1368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y3_check. -/
theorem X1Split70A0X0Y3_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y3_pairs. -/
theorem X1Split70A0X0Y3_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y3Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X1Split70A0X0Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y4Certs : List (Nat × Nat) := [
  (17989, 1448), (23025, 1612), (23219, 1758), (38019, 1607), (51433, 1482),
  (52856, 1462), (54442, 1584), (54457, 1596), (57777, 1520), (80619, 1609),
  (83559, 1645), (92563, 1473), (94031, 1499), (96546, 1560), (98851, 1470),
  (102338, 1549), (106020, 1417), (108190, 1602), (108225, 1625), (108429, 1413),
  (111498, 1517), (116029, 1661), (116038, 1663), (116076, 1720)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y4_check. -/
theorem X1Split70A0X0Y4_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y4_pairs. -/
theorem X1Split70A0X0Y4_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y4Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X1Split70A0X0Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y5Certs : List (Nat × Nat) := [
  (10393, 1908), (10819, 1827), (10832, 1830), (10902, 1889), (10923, 1895),
  (10934, 1899), (12196, 1821), (25406, 1797), (25622, 1962), (27522, 1931),
  (30207, 1865), (56771, 1929), (58334, 1842), (59191, 1867), (60527, 1835),
  (61876, 1822)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y5_check. -/
theorem X1Split70A0X0Y5_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y5_pairs. -/
theorem X1Split70A0X0Y5_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y5Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X1Split70A0X0Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y6Certs : List (Nat × Nat) := [
  (5456, 2076), (5654, 2223), (12178, 2127), (13375, 2125), (27721, 2104),
  (28582, 2086), (30184, 2129), (32015, 2166), (34000, 2095), (35737, 2068),
  (57518, 2172), (58204, 2044), (61294, 2093), (61588, 2091), (65514, 2099),
  (67232, 2062), (67719, 2177), (72606, 2048), (72670, 2081), (74548, 2119)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y6_check. -/
theorem X1Split70A0X0Y6_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y6_pairs. -/
theorem X1Split70A0X0Y6_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y6Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X1Split70A0X0Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y7Certs : List (Nat × Nat) := [
  (2312, 2301), (10494, 2349), (12240, 2438), (34535, 2330), (35603, 2404),
  (37017, 2525), (62127, 2312), (63430, 2317), (63441, 2319), (63513, 2383),
  (63640, 2504), (64588, 2459), (69796, 2470), (71022, 2398), (71380, 2432),
  (75042, 2524)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y7_check. -/
theorem X1Split70A0X0Y7_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y7_pairs. -/
theorem X1Split70A0X0Y7_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y7Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X1Split70A0X0Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y8Certs : List (Nat × Nat) := [
  (13971, 2820), (13976, 2823), (13983, 2825), (24221, 2592), (44350, 2670),
  (44566, 2843), (46171, 2743), (60140, 2665), (60462, 2655), (60521, 2699),
  (60830, 2662), (68787, 2845), (68788, 2846), (78296, 2608), (78346, 2642),
  (84021, 2675)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y8_check. -/
theorem X1Split70A0X0Y8_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y8_pairs. -/
theorem X1Split70A0X0Y8_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk8
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y8Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk8
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact X1Split70A0X0Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y9Certs : List (Nat × Nat) := [
  (12417, 3094), (12430, 3119), (16738, 2945), (21929, 2872), (27734, 2965),
  (27949, 3153), (35001, 3011), (37514, 2930), (37829, 2894), (42763, 2906),
  (42905, 2998), (43381, 3054), (45267, 3051), (72298, 2937), (73567, 3019),
  (75123, 3046), (75402, 2987), (77785, 3058), (79864, 2944), (80938, 2904),
  (84877, 3002), (87049, 2948)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y9_check. -/
theorem X1Split70A0X0Y9_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y9_pairs. -/
theorem X1Split70A0X0Y9_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk9
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y9Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk9
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact X1Split70A0X0Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X0Y10Certs : List (Nat × Nat) := [
  (16122, 3417), (45475, 3180), (45541, 3225), (45611, 3267), (64979, 3194),
  (67440, 3207), (69916, 3239), (69998, 3311), (79497, 3433), (79507, 3435),
  (79518, 3439), (97186, 3285), (97203, 3314), (98873, 3342), (98898, 3358),
  (100990, 3424)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y10_check. -/
theorem X1Split70A0X0Y10_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0Y10_pairs. -/
theorem X1Split70A0X0Y10_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk0 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk0 masks3S512Chunk10
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X0Y10Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks3S512Chunk10
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact X1Split70A0X0Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X0_pairs. -/
theorem X1Split70A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact X1Split70A0X0Y0_pairs x hx y hy hw
  · exact X1Split70A0X0Y1_pairs x hx y hy hw
  · exact X1Split70A0X0Y2_pairs x hx y hy hw
  · exact X1Split70A0X0Y3_pairs x hx y hy hw
  · exact X1Split70A0X0Y4_pairs x hx y hy hw
  · exact X1Split70A0X0Y5_pairs x hx y hy hw
  · exact X1Split70A0X0Y6_pairs x hx y hy hw
  · exact X1Split70A0X0Y7_pairs x hx y hy hw
  · exact X1Split70A0X0Y8_pairs x hx y hy hw
  · exact X1Split70A0X0Y9_pairs x hx y hy hw
  · exact X1Split70A0X0Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y0Certs : List (Nat × Nat) := [
  (6369, 556), (25851, 500), (26120, 331), (27835, 194), (41161, 344),
  (57718, 507), (64030, 459), (64290, 270), (64367, 345), (66424, 553),
  (80612, 192)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y0_check. -/
theorem X1Split70A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y0_pairs. -/
theorem X1Split70A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk0_bound y hy)
  · exact X1Split70A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y1Certs : List (Nat × Nat) := [
  (1833, 586), (1839, 590), (18599, 695), (20433, 717), (20814, 752),
  (37482, 794), (46661, 616), (50636, 618), (51171, 771), (51202, 797)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y1_check. -/
theorem X1Split70A0X1Y1_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y1Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y1_pairs. -/
theorem X1Split70A0X1Y1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk1
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y1Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk1_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk1
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk1_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk1_bound y hy)
  · exact X1Split70A0X1Y1_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y2Certs : List (Nat × Nat) := [
  (8916, 984), (8956, 1017), (8969, 1021), (8978, 1023), (18480, 855),
  (18528, 877), (41962, 980), (47183, 1011)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y2_check. -/
theorem X1Split70A0X1Y2_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y2Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y2_pairs. -/
theorem X1Split70A0X1Y2_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk2
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y2Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk2_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk2
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk2_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk2_bound y hy)
  · exact X1Split70A0X1Y2_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y3Certs : List (Nat × Nat) := [
  (10397, 1380), (19309, 1186), (19434, 1285), (19488, 1310), (20513, 1190),
  (22184, 1232), (24575, 1228), (27300, 1176), (27321, 1200), (43483, 1306),
  (43493, 1315), (46989, 1239), (51679, 1153), (53632, 1132), (55825, 1282),
  (56040, 1135), (58684, 1307), (67616, 1124), (67754, 1220)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y3_check. -/
theorem X1Split70A0X1Y3_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y3Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y3_pairs. -/
theorem X1Split70A0X1Y3_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk3
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y3Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk3_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk3
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk3_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk3_bound y hy)
  · exact X1Split70A0X1Y3_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y4Certs : List (Nat × Nat) := [
  (13472, 1732), (13482, 1733), (14477, 1748), (23245, 1412), (24862, 1518),
  (26646, 1420), (27839, 1597), (41679, 1440), (41766, 1507), (41783, 1509),
  (42097, 1760), (42098, 1761), (65037, 1521), (67399, 1479), (67983, 1555),
  (68526, 1613), (72611, 1411), (79290, 1718)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y4_check. -/
theorem X1Split70A0X1Y4_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y4Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y4_pairs. -/
theorem X1Split70A0X1Y4_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk4,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk4
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y4Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk4_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk4
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk4_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk4_bound y hy)
  · exact X1Split70A0X1Y4_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y5Certs : List (Nat × Nat) := [
  (15310, 1872), (17077, 1991), (17225, 1857), (18799, 1806), (35015, 1985)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y5_check. -/
theorem X1Split70A0X1Y5_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y5Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y5_pairs. -/
theorem X1Split70A0X1Y5_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk5,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk5
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y5Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk5_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk5
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk5_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk5_bound y hy)
  · exact X1Split70A0X1Y5_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y6Certs : List (Nat × Nat) := [
  (4188, 2238), (17040, 2202), (20200, 2094), (20409, 2049), (20697, 2249),
  (38005, 2155), (38035, 2197), (38919, 2176), (40118, 2171), (40211, 2052),
  (40424, 2181), (41995, 2242), (43785, 2237), (45086, 2089), (53376, 2232)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y6_check. -/
theorem X1Split70A0X1Y6_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y6Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y6_pairs. -/
theorem X1Split70A0X1Y6_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk6,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk6
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y6Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk6_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk6
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk6_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk6_bound y hy)
  · exact X1Split70A0X1Y6_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y7Certs : List (Nat × Nat) := [
  (15889, 2518), (16805, 2448), (18244, 2303), (18452, 2493), (19908, 2328),
  (20451, 2546), (22001, 2445), (29366, 2367), (41977, 2313), (43274, 2308),
  (43839, 2519), (45263, 2337), (45511, 2283), (47248, 2373)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y7_check. -/
theorem X1Split70A0X1Y7_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y7Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y7_pairs. -/
theorem X1Split70A0X1Y7_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk7,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk7
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y7Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk7_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk7
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk7_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk7_bound y hy)
  · exact X1Split70A0X1Y7_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y8Certs : List (Nat × Nat) := [
  (9654, 2737), (20067, 2626), (20165, 2706), (30417, 2758), (30423, 2759),
  (30434, 2761), (36181, 2610), (49556, 2629), (49567, 2645)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y8_check. -/
theorem X1Split70A0X1Y8_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y8Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y8_pairs. -/
theorem X1Split70A0X1Y8_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk8,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk8
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk8
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y8Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk8_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk8
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk8_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk8_bound y hy)
  · exact X1Split70A0X1Y8_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y9Certs : List (Nat × Nat) := [
  (19370, 2931), (20898, 2946), (21193, 2888), (25523, 3000), (25891, 2995),
  (33680, 2899), (33804, 2974), (35971, 2910), (36181, 3044), (44382, 2973),
  (47632, 2871), (47671, 2900), (50459, 2992), (53260, 3129), (55202, 2884),
  (56905, 3001)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y9_check. -/
theorem X1Split70A0X1Y9_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y9Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y9_pairs. -/
theorem X1Split70A0X1Y9_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk9,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk9
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk9
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y9Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk9_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk9
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk9_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk9_bound y hy)
  · exact X1Split70A0X1Y9_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split70A0X1Y10Certs : List (Nat × Nat) := [
  (10380, 3349), (11151, 3330), (11234, 3409), (11990, 3344), (23152, 3184),
  (23400, 3371), (35165, 3364), (57291, 3209), (57392, 3271), (66271, 3243)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y10_check. -/
theorem X1Split70A0X1Y10_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y10Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1Y10_pairs. -/
theorem X1Split70A0X1Y10_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks3S512Chunk10,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks2S256Chunk1 masks3S512Chunk10
    (gridWords outerMasks2S256Chunk1 masks3S512Chunk10
      X1M0LeftColumns X1M0RightColumns) X1Split70A0X1Y10Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks3S512Chunk10_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks3S512Chunk10
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks3S512Chunk10_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks3S512Chunk10_bound y hy)
  · exact X1Split70A0X1Y10_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0X1_pairs. -/
theorem X1Split70A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks3S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks3S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact X1Split70A0X1Y0_pairs x hx y hy hw
  · exact X1Split70A0X1Y1_pairs x hx y hy hw
  · exact X1Split70A0X1Y2_pairs x hx y hy hw
  · exact X1Split70A0X1Y3_pairs x hx y hy hw
  · exact X1Split70A0X1Y4_pairs x hx y hy hw
  · exact X1Split70A0X1Y5_pairs x hx y hy hw
  · exact X1Split70A0X1Y6_pairs x hx y hy hw
  · exact X1Split70A0X1Y7_pairs x hx y hy hw
  · exact X1Split70A0X1Y8_pairs x hx y hy hw
  · exact X1Split70A0X1Y9_pairs x hx y hy hw
  · exact X1Split70A0X1Y10_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70A0_pairs. -/
theorem X1Split70A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 3,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split70A0X0_pairs x hx y hy hw
  · exact X1Split70A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split70_check. -/
theorem X1Split70_check : checkSplit m4TX1 (2, 3, 3, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 3 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split70A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split71A0X0Y0Certs : List (Nat × Nat) := [
  (3077, 177), (3133, 466), (3179, 702), (3248, 1152), (4491, 750),
  (5384, 873), (5479, 1592), (5750, 499), (12667, 274), (13945, 151),
  (14005, 445), (14096, 975), (16280, 1041), (17241, 1778), (17258, 1888),
  (17264, 2015), (17500, 519), (17587, 1062), (17651, 1528), (17719, 2123),
  (19239, 513), (19265, 653), (20708, 1610), (22321, 736), (22548, 2633),
  (22819, 1133), (25235, 55), (26725, 1109), (30169, 843), (33847, 2584),
  (33968, 211), (40121, 529), (40150, 675), (40254, 1406), (41458, 691),
  (43147, 433), (43157, 494), (43192, 658), (43194, 666), (43587, 455),
  (43684, 1024), (43786, 1814), (46495, 2887), (47711, 1928), (48725, 56),
  (48976, 1583), (49074, 2594), (49329, 971), (49380, 1318), (49795, 1182),
  (49888, 1970), (49940, 2544), (49992, 3045), (51969, 1168), (52006, 1432),
  (55177, 2667), (57192, 1216), (57675, 1578), (57844, 3286), (58170, 2097),
  (60724, 1591), (60871, 3172), (62232, 159), (64682, 2041), (69606, 68),
  (74360, 3181), (74909, 471), (74910, 474), (75239, 3236), (75366, 579),
  (83092, 73), (83166, 430), (84596, 1198), (84637, 1474), (84722, 2290),
  (85152, 2271), (85156, 2286), (85161, 2316), (86365, 1409), (86815, 1515),
  (88920, 999), (88934, 1119), (88984, 1445), (88986, 1466), (89298, 646),
  (89361, 1047), (89470, 1902), (91811, 157), (91838, 278), (91883, 505),
  (92164, 2862), (93176, 451), (94863, 181), (94880, 265), (95122, 1864),
  (95568, 2043), (97032, 160), (97363, 2606), (97418, 3197), (97651, 1253),
  (97723, 1799), (97906, 175), (98196, 2163), (98203, 2274), (98258, 2882),
  (100370, 2142), (100391, 2371), (104085, 643), (104134, 920), (104332, 2666),
  (106133, 3352), (108203, 2221), (108370, 305), (108672, 2599), (109149, 3005)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X0Y0_check. -/
theorem X1Split71A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X0Y0_pairs. -/
theorem X1Split71A0X0Y0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks2S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split71A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X0_pairs. -/
theorem X1Split71A0X0_pairs : ∀ x ∈ outerMasks2S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split71A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split71A0X1Y0Certs : List (Nat × Nat) := [
  (64, 339), (3102, 313), (3408, 2632), (5745, 475), (8214, 2885),
  (11927, 1016), (11933, 1084), (11934, 1089), (12837, 1296), (14928, 740),
  (15159, 2701), (21116, 1410), (21283, 3072), (22225, 217), (22363, 985),
  (24145, 1287), (24443, 438), (24682, 2193), (24707, 2453), (24815, 126),
  (24866, 375), (24936, 751), (26869, 2300), (27319, 2512), (29436, 1854),
  (29454, 2065), (29489, 2394), (29491, 2437), (29818, 1415), (29859, 1785),
  (29877, 1941), (31458, 741), (31738, 3221), (37641, 1401), (37643, 1405),
  (37838, 3351), (39486, 2315), (41730, 3151), (41789, 173), (42704, 388),
  (43651, 813), (45219, 3200), (48427, 753), (48709, 3289), (51084, 1090),
  (54814, 50), (54834, 146), (55148, 2324), (56450, 2305), (56501, 2891),
  (57877, 140), (57903, 259), (57904, 260), (58073, 1274), (58404, 593),
  (58579, 1832), (60586, 644), (61081, 1007), (61230, 2280), (61304, 3106),
  (61411, 396), (61498, 871), (61598, 1611), (63185, 574), (63523, 94),
  (65261, 91), (65463, 1259), (65531, 1792), (65643, 2941), (67592, 909),
  (69439, 1746), (71007, 540), (74875, 304), (75085, 1626), (77271, 1777)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X1Y0_check. -/
theorem X1Split71A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X1Y0_pairs. -/
theorem X1Split71A0X1Y0_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks2S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split71A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split71A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0X1_pairs. -/
theorem X1Split71A0X1_pairs : ∀ x ∈ outerMasks2S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split71A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71A0_pairs. -/
theorem X1Split71A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split71A0X0_pairs x hx y hy hw
  · exact X1Split71A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split71_check. -/
theorem X1Split71_check : checkSplit m4TX1 (2, 4, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split71A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split72A0X0Y0Certs : List (Nat × Nat) := [
  (317, 732), (372, 356), (877, 134), (880, 248), (964, 64),
  (973, 423), (1433, 1572), (1548, 836), (1742, 24), (2774, 488),
  (2776, 637), (2863, 421), (2866, 641), (3009, 200), (3019, 966),
  (3807, 2573), (3960, 7), (4197, 2577), (4296, 102), (5840, 1101),
  (5842, 1394), (5989, 961), (5992, 1389), (6165, 562), (6174, 1767),
  (6548, 169), (6550, 246), (7319, 3166), (7472, 33), (7829, 3169),
  (7992, 352), (8633, 1564), (9295, 2031), (9296, 2257), (9474, 1774),
  (9476, 2258), (9633, 44), (9651, 1246), (9756, 99), (10301, 298),
  (10931, 292), (11118, 832), (11371, 16), (11377, 137), (11795, 84),
  (11818, 2857), (11973, 46), (11975, 83), (12767, 723), (12900, 6)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0X0Y0_check. -/
theorem X1Split72A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split72A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0X0Y0_pairs. -/
theorem X1Split72A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks2S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split72A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split72A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0X0_pairs. -/
theorem X1Split72A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split72A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split72A0_pairs. -/
theorem X1Split72A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split72A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split72_check. -/
theorem X1Split72_check : checkSplit m4TX1 (2, 5, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split72A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split73A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0X0Y0_check. -/
theorem X1Split73A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split73A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0X0Y0_pairs. -/
theorem X1Split73A0X0Y0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 6
    outerMasks2S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split73A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks2S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks2S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks2S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks2S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split73A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0X0_pairs. -/
theorem X1Split73A0X0_pairs : ∀ x ∈ outerMasks2S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split73A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split73A0_pairs. -/
theorem X1Split73A0_pairs : ∀ x ∈ masksOfWt 30 2, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 6 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks2S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks2S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl
  · exact X1Split73A0X0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split73_check. -/
theorem X1Split73_check : checkSplit m4TX1 (2, 6, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 2 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split73A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split74A0X0Y0Certs : List (Nat × Nat) := [
  (275, 2968), (332, 3510), (595, 2980), (954, 1660), (1093, 3456),
  (1356, 2803), (1644, 1715), (1786, 2757), (1832, 3527)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X0Y0_check. -/
theorem X1Split74A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split74A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X0Y0_pairs. -/
theorem X1Split74A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split74A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split74A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X0_pairs. -/
theorem X1Split74A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split74A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split74A0X1Y0Certs : List (Nat × Nat) := [
  (240, 3281), (557, 3335), (684, 1727), (785, 2725), (956, 1754),
  (969, 3350), (1049, 2977), (1300, 2083), (1768, 2835), (1789, 2078),
  (1901, 819)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X1Y0_check. -/
theorem X1Split74A0X1Y0_check : checkGrid m4TX1 censusX1 1 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split74A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X1Y0_pairs. -/
theorem X1Split74A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split74A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split74A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0X1_pairs. -/
theorem X1Split74A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split74A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74A0_pairs. -/
theorem X1Split74A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 5 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split74A0X0_pairs x hx y hy hw
  · exact X1Split74A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split74_check. -/
theorem X1Split74_check : checkSplit m4TX1 (3, 0, 5, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split74A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split75A0X0Y0Certs : List (Nat × Nat) := [
  (1909, 2890), (4026, 1230), (5233, 1480), (5245, 2244), (5478, 1744),
  (9960, 1338), (9962, 1298), (9978, 3347), (11235, 2482), (11236, 1087),
  (11663, 1759), (11812, 1288), (12144, 470), (13500, 3254), (14992, 3104),
  (16482, 1762), (16627, 667), (17021, 908), (17861, 3043), (17867, 3157),
  (17879, 2972), (18432, 2239), (20201, 2976), (21709, 2460), (21718, 3049),
  (22560, 2837), (28917, 854), (32790, 1680), (32792, 1635), (32796, 934),
  (35631, 2510), (35632, 2024), (36777, 2844), (37076, 707), (37623, 1080),
  (39752, 1464), (40680, 3247), (40692, 3464), (40698, 600), (41309, 3345),
  (43227, 2663), (43496, 3021), (45635, 2352), (45828, 2848), (46033, 1469),
  (47417, 1085), (49331, 187), (49337, 2776), (49343, 3375), (50268, 2978),
  (52937, 767), (56678, 389), (56694, 2346), (57239, 223), (58082, 3529)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X0Y0_check. -/
theorem X1Split75A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split75A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X0Y0_pairs. -/
theorem X1Split75A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split75A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S2048Chunk0 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split75A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X0_pairs. -/
theorem X1Split75A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split75A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split75A0X1Y0Certs : List (Nat × Nat) := [
  (947, 1894), (1326, 824), (7202, 2794), (7206, 2718), (7212, 1632),
  (8500, 1180), (8727, 2750), (10650, 3343), (12061, 2620), (12086, 2824),
  (13829, 3346), (14029, 2444), (14255, 1535), (15037, 2011), (16733, 1221),
  (16737, 3337), (16739, 3336), (17166, 2434), (17612, 2356), (20526, 3497),
  (20532, 3301), (20538, 2710), (20723, 2020), (22119, 1493), (22120, 2344),
  (23033, 1655), (23567, 543), (23573, 3463), (23577, 2658), (24840, 1425),
  (31626, 3458), (33903, 1094), (33914, 911), (34691, 604), (38628, 3158),
  (38776, 2159), (38883, 1817), (39011, 2227), (39027, 2121), (39029, 2118),
  (39209, 3431), (42812, 346), (43903, 2559), (44116, 3056), (44854, 3256),
  (44855, 3355), (46421, 1020), (46662, 2226), (46704, 1349), (47020, 2554),
  (48942, 3284), (51233, 888), (57217, 1873), (57230, 1234), (59627, 1344)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X1Y0_check. -/
theorem X1Split75A0X1Y0_check : checkGrid m4TX1 censusX1 1 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split75A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X1Y0_pairs. -/
theorem X1Split75A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split75A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S2048Chunk1 masks1S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split75A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0X1_pairs. -/
theorem X1Split75A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split75A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75A0_pairs. -/
theorem X1Split75A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 4 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split75A0X0_pairs x hx y hy hw
  · exact X1Split75A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split75_check. -/
theorem X1Split75_check : checkSplit m4TX1 (3, 1, 4, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split75A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X0Y0Certs : List (Nat × Nat) := [
  (11078, 2653), (27735, 2293), (28723, 811), (41204, 2116), (73528, 154),
  (75715, 468), (77057, 2607), (77138, 1600), (79317, 1738), (79335, 3333),
  (79440, 3334), (79538, 1151), (79593, 1222), (80250, 1347), (80918, 769),
  (81067, 3230), (89064, 1255), (91500, 1217), (91770, 2749)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X0Y0_check. -/
theorem X1Split76A0X0Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X0Y0_pairs. -/
theorem X1Split76A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk0 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X0_pairs. -/
theorem X1Split76A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X1Y0Certs : List (Nat × Nat) := [
  (12064, 3328), (48867, 3340), (48879, 2756), (48885, 1747), (48990, 1751),
  (49126, 1297), (67091, 825), (75534, 1824), (80090, 441), (83137, 1743),
  (96857, 1831), (96945, 2017), (100419, 922)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X1Y0_check. -/
theorem X1Split76A0X1Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X1Y0_pairs. -/
theorem X1Split76A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk1 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X1_pairs. -/
theorem X1Split76A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X2Y0Certs : List (Nat × Nat) := [
  (3217, 1990), (10706, 2501), (12652, 261), (16134, 1419), (20843, 3041),
  (25552, 2877), (40414, 2940), (41032, 1431), (48076, 2248), (49138, 3237),
  (60469, 2831), (60901, 2975), (60917, 3039), (61064, 3154), (61329, 3524),
  (61333, 2911), (71665, 2840), (71677, 2318), (77884, 1586), (78022, 3296),
  (79377, 1741), (95248, 3520)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X2Y0_check. -/
theorem X1Split76A0X2Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X2Y0_pairs. -/
theorem X1Split76A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X2Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk2_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk2 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X2_pairs. -/
theorem X1Split76A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X3Y0Certs : List (Nat × Nat) := [
  (1350, 414), (1352, 772), (10927, 458), (18792, 1070), (22334, 3238),
  (22451, 2652), (30169, 311), (31473, 2077), (31584, 2222), (31590, 2830),
  (31694, 2082), (31749, 2122), (32627, 1783), (34836, 915), (34842, 1658),
  (36496, 3130), (47369, 3519), (47381, 3040), (49101, 123), (53271, 3422),
  (53343, 2224)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X3Y0_check. -/
theorem X1Split76A0X3Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X3Y0_pairs. -/
theorem X1Split76A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X3Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk3_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk3 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X3_pairs. -/
theorem X1Split76A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X4Y0Certs : List (Nat × Nat) := [
  (15497, 1098), (15650, 3323), (39552, 1992), (63071, 3428), (63946, 789),
  (63960, 1701), (64011, 2597), (64098, 3182), (64319, 3226)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X4Y0_check. -/
theorem X1Split76A0X4Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X4Y0_pairs. -/
theorem X1Split76A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X4Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk4_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk4 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X4_pairs. -/
theorem X1Split76A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X5Y0Certs : List (Nat × Nat) := [
  (9747, 387), (17121, 1065), (34795, 3324), (53997, 852), (54006, 3174),
  (54093, 2591), (54210, 315), (54314, 2637), (66586, 2384), (68771, 554)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X5Y0_check. -/
theorem X1Split76A0X5Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X5Y0_pairs. -/
theorem X1Split76A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X5Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk5_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk5 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X5_pairs. -/
theorem X1Split76A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X6Y0Certs : List (Nat × Nat) := [
  (4690, 2967), (16314, 1471), (19538, 2137), (20651, 1763), (25339, 572),
  (41349, 705), (49435, 1049), (49720, 1014), (54943, 2836), (75394, 931),
  (75664, 2595), (80881, 1456)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X6Y0_check. -/
theorem X1Split76A0X6Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X6Y0_pairs. -/
theorem X1Split76A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X6Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk6_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk6 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X6_pairs. -/
theorem X1Split76A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X7Y0Certs : List (Nat × Nat) := [
  (11378, 1659), (11382, 953), (11457, 816), (11679, 913), (11727, 2726),
  (16318, 1068), (17680, 2372), (19450, 2063), (20367, 2753), (35315, 2288),
  (37345, 2651), (41434, 669), (47527, 2336), (48105, 1657), (55118, 2672),
  (62609, 235), (84629, 1205), (85960, 2368)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X7Y0_check. -/
theorem X1Split76A0X7Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X7Y0_pairs. -/
theorem X1Split76A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X7Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk7_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk7 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X7_pairs. -/
theorem X1Split76A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X8Y0Certs : List (Nat × Nat) := [
  (11977, 2870), (17564, 1018), (23330, 2619), (29537, 3360), (32314, 3429),
  (44830, 3522), (45257, 765), (45312, 2643), (45376, 3270), (45602, 881),
  (45657, 795), (56023, 1510), (63087, 3185), (63233, 790), (72681, 340),
  (72720, 2614), (74273, 2833), (85236, 1453), (97604, 338)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X8Y0_check. -/
theorem X1Split76A0X8Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X8Y0_pairs. -/
theorem X1Split76A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X8Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk8_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk8 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X8_pairs. -/
theorem X1Split76A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X9Y0Certs : List (Nat × Nat) := [
  (10127, 955), (10131, 1664), (34398, 626), (37978, 1055), (39974, 3025),
  (51516, 1993), (57692, 1019), (57790, 3325), (59161, 342), (59177, 1706),
  (59228, 2613), (59315, 3206), (59593, 882), (61464, 690), (69606, 749),
  (71776, 2966), (72137, 3037), (72143, 3152), (72149, 3521), (72208, 2979),
  (73099, 124), (77102, 1336), (77112, 2755), (78914, 1280), (94539, 336),
  (94754, 2644), (97040, 392), (103412, 2909), (103471, 3155)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X9Y0_check. -/
theorem X1Split76A0X9Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X9Y0_pairs. -/
theorem X1Split76A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X9Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk9_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk9 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X9_pairs. -/
theorem X1Split76A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X10Y0Certs : List (Nat × Nat) := [
  (533, 1601), (17108, 1505), (19197, 652), (19690, 1236), (26757, 3348),
  (28157, 2115), (28271, 2834), (35958, 907), (48741, 1973), (71350, 322),
  (71498, 3195), (76183, 1883), (104401, 3193), (104542, 122), (104555, 321),
  (104774, 759), (104833, 3297)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X10Y0_check. -/
theorem X1Split76A0X10Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X10Y0_pairs. -/
theorem X1Split76A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X10Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk10_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk10 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X10_pairs. -/
theorem X1Split76A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X11Y0_check. -/
theorem X1Split76A0X11Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X11Y0_pairs. -/
theorem X1Split76A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X11Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk11_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk11 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X11_pairs. -/
theorem X1Split76A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X12Y0Certs : List (Nat × Nat) := [
  (4536, 1340), (5430, 1343), (5436, 1750), (6345, 1745), (12813, 511),
  (14143, 1269), (16434, 2207), (20660, 1652), (21876, 1820), (34734, 1342),
  (43304, 2403), (47521, 2446), (52073, 3069), (55132, 2849), (62424, 1271),
  (86325, 1009), (86650, 1531), (97479, 1950), (98122, 1885), (105955, 3528)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X12Y0_check. -/
theorem X1Split76A0X12Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X12Y0_pairs. -/
theorem X1Split76A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X12Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk12_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk12 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X12_pairs. -/
theorem X1Split76A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X13Y0Certs : List (Nat × Nat) := [
  (12333, 1146), (12345, 2745), (12444, 1740), (12450, 2742), (12537, 2748),
  (12677, 3199), (12875, 1599), (18762, 2424)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X13Y0_check. -/
theorem X1Split76A0X13Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X13Y0_pairs. -/
theorem X1Split76A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X13Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk13_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk13 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X13_pairs. -/
theorem X1Split76A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X14Y0Certs : List (Nat × Nat) := [
  (27277, 2201), (39479, 196), (46995, 770), (46997, 412), (47245, 391),
  (47397, 341), (47413, 1638), (49726, 1891), (58667, 3253), (63994, 272),
  (68493, 2429), (70068, 347), (72885, 3079), (82757, 815), (82818, 3248),
  (83221, 812), (84872, 978), (90567, 602), (90987, 1650), (91062, 1717),
  (91080, 3312), (91170, 1653), (91338, 808), (106585, 2325)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X14Y0_check. -/
theorem X1Split76A0X14Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X14Y0_pairs. -/
theorem X1Split76A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X14Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk14_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk14 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X14_pairs. -/
theorem X1Split76A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X15Y0Certs : List (Nat × Nat) := [
  (405, 3525), (6570, 1707), (6576, 349), (24860, 2420)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X15Y0_check. -/
theorem X1Split76A0X15Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X15Y0_pairs. -/
theorem X1Split76A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X15Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk15_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk15 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X15_pairs. -/
theorem X1Split76A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X16Y0Certs : List (Nat × Nat) := [
  (5634, 335), (33968, 1608), (34632, 810), (34785, 3313), (36777, 1756),
  (36783, 2763), (66572, 1637), (66972, 1604), (66978, 2611), (66984, 3204),
  (66988, 411), (74924, 914), (76226, 1381), (78079, 1092), (81160, 1961),
  (83664, 2385), (91425, 393), (93647, 2668), (93657, 827), (99912, 2389),
  (108690, 1893), (108745, 1897)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X16Y0_check. -/
theorem X1Split76A0X16Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X16Y0_pairs. -/
theorem X1Split76A0X16Y0_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X16Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk16_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk16_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk16 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk16_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk16_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X16_pairs. -/
theorem X1Split76A0X16_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X17Y0Certs : List (Nat × Nat) := [
  (885, 601), (887, 818), (942, 2661), (1029, 3246), (1287, 814),
  (4596, 1512), (15441, 1581), (15453, 3292), (17255, 532), (36941, 766),
  (36974, 3300)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X17Y0_check. -/
theorem X1Split76A0X17Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X17Y0_pairs. -/
theorem X1Split76A0X17Y0_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X17Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk17_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk17_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk17 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk17_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk17_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X17_pairs. -/
theorem X1Split76A0X17_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X18Y0Certs : List (Nat × Nat) := [
  (15490, 2915), (20742, 1739), (20881, 2114), (21033, 3427), (21248, 2832),
  (21254, 3423), (21298, 3430), (22187, 738), (22252, 2636), (23847, 2838),
  (30164, 480), (30379, 2650), (33866, 2746), (41639, 1163), (43672, 456),
  (47610, 3136), (54527, 2019), (54856, 2747), (56793, 688), (76531, 254),
  (83197, 571), (86524, 1449), (89079, 1836), (92132, 1548), (95125, 2985),
  (95479, 1794), (100442, 2298), (106109, 3413)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X18Y0_check. -/
theorem X1Split76A0X18Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X18Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X18Y0_pairs. -/
theorem X1Split76A0X18Y0_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X18Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk18_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk18_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk18 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk18_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk18_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X18Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X18_pairs. -/
theorem X1Split76A0X18_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X18Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X19Y0Certs : List (Nat × Nat) := [
  (5761, 476), (21892, 2055), (26845, 1868), (27154, 2549), (39499, 337)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X19Y0_check. -/
theorem X1Split76A0X19Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X19Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X19Y0_pairs. -/
theorem X1Split76A0X19Y0_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X19Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk19_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk19_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk19 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk19_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk19_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X19Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X19_pairs. -/
theorem X1Split76A0X19_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X19Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X20Y0Certs : List (Nat × Nat) := [
  (507, 2724), (582, 2657), (699, 3244), (797, 544), (852, 952),
  (1038, 916), (20247, 3353), (20259, 1765), (22287, 809), (33648, 327),
  (33650, 786), (33654, 1698), (33660, 2585), (33765, 2601), (67860, 320),
  (67927, 2604), (68793, 541), (69089, 1654), (75366, 2664), (76326, 1147),
  (76496, 1742), (79942, 2841), (79948, 3432), (101983, 1202), (105281, 1795)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X20Y0_check. -/
theorem X1Split76A0X20Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X20Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X20Y0_pairs. -/
theorem X1Split76A0X20Y0_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X20Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk20_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk20_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk20 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk20_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk20_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X20Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X20_pairs. -/
theorem X1Split76A0X20_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X20Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split76A0X21Y0Certs : List (Nat × Nat) := [
  (10444, 158), (11954, 1319), (14126, 2040), (16132, 1812), (19489, 54),
  (23322, 1651), (31378, 745), (31729, 1700), (45306, 1292), (45308, 1339),
  (45312, 1753), (45387, 1749), (45405, 3341), (49936, 2397)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X21Y0_check. -/
theorem X1Split76A0X21Y0_check : checkGrid m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X21Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X21Y0_pairs. -/
theorem X1Split76A0X21Y0_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 1 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns) X1Split76A0X21Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk21_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M1Left_bound x (outerMasks3S256Chunk21_bound x hx)
  · intro y hy
    exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 1 outerMasks3S256Chunk21 masks2S512Chunk0
      X1M1LeftColumns X1M1RightColumns
    · decide
    · exact outerMasks3S256Chunk21_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M1Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M1Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M1Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M1Left_eq
    · exact X1M1Right_eq
    · intro x hx
      exact X1M1Left_bound x (outerMasks3S256Chunk21_bound x hx)
    · intro y hy
      exact X1M1Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split76A0X21Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0X21_pairs. -/
theorem X1Split76A0X21_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split76A0X21Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76A0_pairs. -/
theorem X1Split76A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 1 x y 0) = 3 →
      sweepAccept m4TX1 1 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact X1Split76A0X0_pairs x hx y hy hw
  · exact X1Split76A0X1_pairs x hx y hy hw
  · exact X1Split76A0X2_pairs x hx y hy hw
  · exact X1Split76A0X3_pairs x hx y hy hw
  · exact X1Split76A0X4_pairs x hx y hy hw
  · exact X1Split76A0X5_pairs x hx y hy hw
  · exact X1Split76A0X6_pairs x hx y hy hw
  · exact X1Split76A0X7_pairs x hx y hy hw
  · exact X1Split76A0X8_pairs x hx y hy hw
  · exact X1Split76A0X9_pairs x hx y hy hw
  · exact X1Split76A0X10_pairs x hx y hy hw
  · exact X1Split76A0X11_pairs x hx y hy hw
  · exact X1Split76A0X12_pairs x hx y hy hw
  · exact X1Split76A0X13_pairs x hx y hy hw
  · exact X1Split76A0X14_pairs x hx y hy hw
  · exact X1Split76A0X15_pairs x hx y hy hw
  · exact X1Split76A0X16_pairs x hx y hy hw
  · exact X1Split76A0X17_pairs x hx y hy hw
  · exact X1Split76A0X18_pairs x hx y hy hw
  · exact X1Split76A0X19_pairs x hx y hy hw
  · exact X1Split76A0X20_pairs x hx y hy hw
  · exact X1Split76A0X21_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split76_check. -/
theorem X1Split76_check : checkSplit m4TX1 (3, 2, 3, 1) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M1Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M1Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M1_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split76A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X0Y0Certs : List (Nat × Nat) := [
  (27584, 989), (27733, 2273), (28862, 820), (42245, 262), (52788, 840),
  (57635, 1264), (58978, 1575), (59137, 3186), (73595, 429), (77138, 761),
  (77408, 3196), (79366, 1123), (79378, 1219), (80145, 567), (80952, 222),
  (89018, 1782), (91623, 1737)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X0Y0_check. -/
theorem X1Split77A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X0Y0_pairs. -/
theorem X1Split77A0X0Y0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk0 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk0_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk0 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk0_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X0_pairs. -/
theorem X1Split77A0X0_pairs : ∀ x ∈ outerMasks3S256Chunk0, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X1Y0Certs : List (Nat × Nat) := [
  (28367, 492), (48942, 1295), (49092, 2751), (65980, 1901), (66011, 2269),
  (75487, 1403), (75536, 1791), (76844, 1804), (76907, 2452), (79027, 1862),
  (80066, 155), (80330, 1840), (83360, 1755), (96848, 1781), (100178, 662)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X1Y0_check. -/
theorem X1Split77A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X1Y0_pairs. -/
theorem X1Split77A0X1Y0_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk1 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk1_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk1 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk1_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X1_pairs. -/
theorem X1Split77A0X1_pairs : ∀ x ∈ outerMasks3S256Chunk1, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X2Y0Certs : List (Nat × Nat) := [
  (12661, 253), (22750, 673), (40414, 2959), (41130, 1429), (48151, 2039),
  (48799, 428), (53071, 36), (61290, 2912), (61305, 3149), (67906, 252),
  (71682, 2381), (75332, 399), (75608, 2587), (77871, 69), (79372, 1150),
  (95211, 2867)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X2Y0_check. -/
theorem X1Split77A0X2Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X2Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X2Y0_pairs. -/
theorem X1Split77A0X2Y0_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk2 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk2 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X2Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk2_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk2 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk2_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk2_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X2Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X2_pairs. -/
theorem X1Split77A0X2_pairs : ∀ x ∈ outerMasks3S256Chunk2, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X2Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X3Y0Certs : List (Nat × Nat) := [
  (1352, 255), (1468, 870), (10821, 2869), (11052, 983), (22274, 472),
  (22451, 1644), (27387, 3212), (30152, 737), (31620, 2036), (31632, 2079),
  (32837, 1254), (34917, 603), (36218, 584), (47385, 3150), (48738, 119),
  (53446, 2829)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X3Y0_check. -/
theorem X1Split77A0X3Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X3Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X3Y0_pairs. -/
theorem X1Split77A0X3Y0_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk3 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk3 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X3Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk3_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk3 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk3_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk3_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X3Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X3_pairs. -/
theorem X1Split77A0X3_pairs : ∀ x ∈ outerMasks3S256Chunk3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X3Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X4Y0Certs : List (Nat × Nat) := [
  (4515, 884), (5390, 926), (5573, 2588), (15396, 967), (63066, 3332),
  (64085, 748), (64300, 2596), (66314, 1118)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X4Y0_check. -/
theorem X1Split77A0X4Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X4Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X4Y0_pairs. -/
theorem X1Split77A0X4Y0_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk4 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk4 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X4Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk4_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk4 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk4_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk4_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X4Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X4_pairs. -/
theorem X1Split77A0X4_pairs : ∀ x ∈ outerMasks3S256Chunk4, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X4Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X5Y0Certs : List (Nat × Nat) := [
  (26740, 1183), (54094, 846), (54347, 3173), (68849, 614)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X5Y0_check. -/
theorem X1Split77A0X5Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X5Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X5Y0_pairs. -/
theorem X1Split77A0X5Y0_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk5 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk5 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X5Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk5_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk5 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk5_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk5_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X5Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X5_pairs. -/
theorem X1Split77A0X5_pairs : ∀ x ∈ outerMasks3S256Chunk5, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X5Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X6Y0Certs : List (Nat × Nat) := [
  (4692, 2382), (5679, 144), (14258, 2322), (16335, 1427), (17414, 96),
  (17679, 1784), (19349, 1224), (41373, 257), (41654, 2276), (43594, 497),
  (43830, 2279), (47649, 1407), (49435, 1788), (49678, 464), (49783, 1114),
  (55187, 2839), (75273, 120), (80720, 1455)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X6Y0_check. -/
theorem X1Split77A0X6Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X6Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X6Y0_pairs. -/
theorem X1Split77A0X6Y0_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk6 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk6 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X6Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk6_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk6 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk6_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk6_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X6Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X6_pairs. -/
theorem X1Split77A0X6_pairs : ∀ x ∈ outerMasks3S256Chunk6, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X6Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X7Y0Certs : List (Nat × Nat) := [
  (11421, 578), (11578, 1656), (12799, 1027), (12867, 1546), (14101, 1006),
  (19450, 2071), (20227, 1267), (41449, 648), (47958, 570), (58102, 1476),
  (84629, 1423), (86035, 2358)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X7Y0_check. -/
theorem X1Split77A0X7Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X7Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X7Y0_pairs. -/
theorem X1Split77A0X7Y0_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk7 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk7 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X7Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk7_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk7 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk7_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk7_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X7Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X7_pairs. -/
theorem X1Split77A0X7_pairs : ∀ x ∈ outerMasks3S256Chunk7, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X7Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X8Y0Certs : List (Nat × Nat) := [
  (12127, 2875), (17575, 974), (31337, 117), (32612, 3250), (45401, 867),
  (45654, 3203), (57544, 651), (63333, 1588), (69335, 925), (69577, 3188),
  (72683, 212), (74268, 2120), (75167, 2455), (78160, 1904), (97475, 191)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X8Y0_check. -/
theorem X1Split77A0X8Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X8Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X8Y0_pairs. -/
theorem X1Split77A0X8Y0_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk8 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk8 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X8Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk8_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk8 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk8_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk8_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X8Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X8_pairs. -/
theorem X1Split77A0X8_pairs : ∀ x ∈ outerMasks3S256Chunk8, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X8Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X9Y0Certs : List (Nat × Nat) := [
  (10125, 642), (10131, 655), (27031, 323), (27241, 1693), (37010, 190),
  (38133, 1829), (39896, 2075), (57608, 1083), (57790, 2736), (59422, 1606),
  (59575, 3205), (64962, 773), (68239, 2863), (69857, 1585), (72155, 2865),
  (72171, 2970), (73096, 114), (77223, 1341), (78959, 1305), (94809, 3202),
  (97078, 384), (100794, 2066), (103529, 3518)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X9Y0_check. -/
theorem X1Split77A0X9Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X9Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X9Y0_pairs. -/
theorem X1Split77A0X9Y0_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk9 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk9 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X9Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk9_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk9 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk9_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk9_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X9Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X9_pairs. -/
theorem X1Split77A0X9_pairs : ∀ x ∈ outerMasks3S256Chunk9, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X9Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X10Y0Certs : List (Nat × Nat) := [
  (19264, 649), (19805, 1363), (25554, 2229), (26756, 1291), (28163, 2220),
  (64701, 2161), (71350, 90), (71411, 374), (104406, 70), (104459, 319)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X10Y0_check. -/
theorem X1Split77A0X10Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X10Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X10Y0_pairs. -/
theorem X1Split77A0X10Y0_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk10 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk10 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X10Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk10_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk10 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk10_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk10_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X10Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X10_pairs. -/
theorem X1Split77A0X10_pairs : ∀ x ∈ outerMasks3S256Chunk10, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X10Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X11Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X11Y0_check. -/
theorem X1Split77A0X11Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X11Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X11Y0_pairs. -/
theorem X1Split77A0X11Y0_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk11 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk11 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X11Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk11_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk11 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk11_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk11_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X11Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X11_pairs. -/
theorem X1Split77A0X11_pairs : ∀ x ∈ outerMasks3S256Chunk11, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X11Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X12Y0Certs : List (Nat × Nat) := [
  (5442, 1294), (6299, 1225), (12650, 189), (14143, 1299), (16434, 2347),
  (20703, 1587), (22705, 444), (34580, 1263), (43676, 976), (47755, 2360),
  (49614, 145), (49644, 286), (52089, 2231), (86606, 220), (86692, 657),
  (89225, 263), (89372, 1126), (94953, 647), (95597, 2291), (97479, 213),
  (98062, 1064), (98182, 2057), (106116, 3183)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X12Y0_check. -/
theorem X1Split77A0X12Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X12Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X12Y0_pairs. -/
theorem X1Split77A0X12Y0_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk12 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk12 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X12Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk12_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk12 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk12_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk12_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X12Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X12_pairs. -/
theorem X1Split77A0X12_pairs : ∀ x ∈ outerMasks3S256Chunk12, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X12Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X13Y0Certs : List (Nat × Nat) := [
  (12372, 1113), (12387, 1214), (12688, 385), (19050, 2423)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X13Y0_check. -/
theorem X1Split77A0X13Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X13Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X13Y0_pairs. -/
theorem X1Split77A0X13Y0_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk13 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk13 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X13Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk13_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk13 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk13_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk13_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X13Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X13_pairs. -/
theorem X1Split77A0X13_pairs : ∀ x ∈ outerMasks3S256Chunk13, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X13Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X14Y0Certs : List (Nat × Nat) := [
  (4690, 2359), (27357, 2898), (28787, 400), (28963, 1576), (39194, 231),
  (47018, 210), (47125, 768), (49875, 1811), (71847, 377), (72887, 1438),
  (82761, 577), (83189, 548), (91006, 491), (91017, 539), (108555, 1426)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X14Y0_check. -/
theorem X1Split77A0X14Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X14Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X14Y0_pairs. -/
theorem X1Split77A0X14Y0_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk14 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk14 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X14Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk14_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk14 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk14_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk14_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X14Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X14_pairs. -/
theorem X1Split77A0X14_pairs : ∀ x ∈ outerMasks3S256Chunk14, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X14Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X15Y0Certs : List (Nat × Nat) := [
  (378, 2861), (6886, 2617), (12075, 2282), (16374, 1787)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X15Y0_check. -/
theorem X1Split77A0X15Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X15Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X15Y0_pairs. -/
theorem X1Split77A0X15Y0_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk15 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk15 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X15Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk15_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk15 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk15_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk15_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X15Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X15_pairs. -/
theorem X1Split77A0X15_pairs : ∀ x ∈ outerMasks3S256Chunk15, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X15Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X16Y0Certs : List (Nat × Nat) := [
  (5250, 174), (9167, 178), (34290, 2612), (34467, 537), (36773, 1404),
  (36783, 1441), (64963, 783), (65166, 2581), (66583, 172), (66589, 186),
  (74986, 903), (80144, 547), (81066, 853), (83915, 2964), (91420, 373),
  (93947, 3251), (108614, 2016), (108745, 3412)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X16Y0_check. -/
theorem X1Split77A0X16Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X16Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X16Y0_pairs. -/
theorem X1Split77A0X16Y0_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk16 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk16 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X16Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk16_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk16 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk16_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk16_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X16Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X16_pairs. -/
theorem X1Split77A0X16_pairs : ∀ x ∈ outerMasks3S256Chunk16, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X16Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X17Y0Certs : List (Nat × Nat) := [
  (986, 599), (1236, 2660), (8535, 1667), (14851, 324), (15141, 2582),
  (15225, 22), (17156, 1111), (32583, 2942), (36603, 334)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X17Y0_check. -/
theorem X1Split77A0X17Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X17Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X17Y0_pairs. -/
theorem X1Split77A0X17Y0_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk17 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk17 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X17Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk17_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk17 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk17_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk17_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X17Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X17_pairs. -/
theorem X1Split77A0X17_pairs : ∀ x ∈ outerMasks3S256Chunk17, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X17Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X18Y0Certs : List (Nat × Nat) := [
  (12862, 1477), (13012, 2981), (15613, 2902), (21186, 2053), (21203, 2219),
  (22339, 844), (23814, 2228), (30181, 902), (33860, 2656), (40258, 1416),
  (41429, 546), (43672, 969), (46193, 439), (47610, 1120), (55171, 2616),
  (58039, 1026), (76171, 250), (83197, 580), (89461, 1816), (92083, 1972),
  (92176, 2917), (95056, 1325), (95174, 2396), (95480, 1266), (97960, 446),
  (98010, 714), (100431, 2866)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X18Y0_check. -/
theorem X1Split77A0X18Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X18Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X18Y0_pairs. -/
theorem X1Split77A0X18Y0_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk18 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk18 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X18Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk18_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk18 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk18_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk18_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X18Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X18_pairs. -/
theorem X1Split77A0X18_pairs : ∀ x ∈ outerMasks3S256Chunk18, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X18Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X19Y0Certs : List (Nat × Nat) := [
  (22055, 2051), (27085, 597), (27214, 1446), (29710, 674), (29893, 2084),
  (39215, 343)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X19Y0_check. -/
theorem X1Split77A0X19Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X19Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X19Y0_pairs. -/
theorem X1Split77A0X19Y0_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk19 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk19 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X19Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk19_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk19 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk19_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk19_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X19Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X19_pairs. -/
theorem X1Split77A0X19_pairs : ∀ x ∈ outerMasks3S256Chunk19, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X19Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X20Y0Certs : List (Nat × Nat) := [
  (528, 496), (538, 542), (1032, 869), (8918, 1272), (20252, 1439),
  (22282, 504), (25663, 3442), (33551, 310), (33749, 1577), (34900, 520),
  (60613, 784), (60873, 3176), (67868, 74), (68880, 807), (75676, 3245),
  (76332, 1215), (79936, 2287), (79948, 2388), (102094, 2046)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X20Y0_check. -/
theorem X1Split77A0X20Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X20Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X20Y0_pairs. -/
theorem X1Split77A0X20Y0_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk20 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk20 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X20Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk20_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk20 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk20_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk20_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X20Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X20_pairs. -/
theorem X1Split77A0X20_pairs : ∀ x ∈ outerMasks3S256Chunk20, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X20Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split77A0X21Y0Certs : List (Nat × Nat) := [
  (8536, 1694), (8673, 3175), (11916, 968), (18479, 1226), (19161, 139),
  (23316, 1603), (31378, 317), (31674, 2593), (45467, 1335), (45667, 3339),
  (53444, 2767)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X21Y0_check. -/
theorem X1Split77A0X21Y0_check : checkGrid m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X21Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X21Y0_pairs. -/
theorem X1Split77A0X21Y0_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masks2S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 3
    outerMasks3S256Chunk21 masks2S512Chunk0
    (gridWords outerMasks3S256Chunk21 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split77A0X21Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S256Chunk21_bound
  · exact masks2S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S256Chunk21 masks2S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S256Chunk21_bound
    · exact masks2S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S256Chunk21_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks2S512Chunk0_bound y hy)
  · exact X1Split77A0X21Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0X21_pairs. -/
theorem X1Split77A0X21_pairs : ∀ x ∈ outerMasks3S256Chunk21, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks2S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks2S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split77A0X21Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77A0_pairs. -/
theorem X1Split77A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 2,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 3 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S256_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S256Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact X1Split77A0X0_pairs x hx y hy hw
  · exact X1Split77A0X1_pairs x hx y hy hw
  · exact X1Split77A0X2_pairs x hx y hy hw
  · exact X1Split77A0X3_pairs x hx y hy hw
  · exact X1Split77A0X4_pairs x hx y hy hw
  · exact X1Split77A0X5_pairs x hx y hy hw
  · exact X1Split77A0X6_pairs x hx y hy hw
  · exact X1Split77A0X7_pairs x hx y hy hw
  · exact X1Split77A0X8_pairs x hx y hy hw
  · exact X1Split77A0X9_pairs x hx y hy hw
  · exact X1Split77A0X10_pairs x hx y hy hw
  · exact X1Split77A0X11_pairs x hx y hy hw
  · exact X1Split77A0X12_pairs x hx y hy hw
  · exact X1Split77A0X13_pairs x hx y hy hw
  · exact X1Split77A0X14_pairs x hx y hy hw
  · exact X1Split77A0X15_pairs x hx y hy hw
  · exact X1Split77A0X16_pairs x hx y hy hw
  · exact X1Split77A0X17_pairs x hx y hy hw
  · exact X1Split77A0X18_pairs x hx y hy hw
  · exact X1Split77A0X19_pairs x hx y hy hw
  · exact X1Split77A0X20_pairs x hx y hy hw
  · exact X1Split77A0X21_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split77_check. -/
theorem X1Split77_check : checkSplit m4TX1 (3, 3, 2, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 2 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split77A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split78A0X0Y0Certs : List (Nat × Nat) := [
  (3647, 727), (3659, 3164), (4062, 354), (9981, 1241), (14611, 20),
  (16951, 13), (16975, 2028), (17321, 302), (17333, 1570), (17406, 106),
  (17878, 2852), (18858, 830), (22262, 23), (22278, 828), (22898, 161),
  (22905, 564), (24791, 295), (24807, 2570), (24846, 108), (30821, 293),
  (32791, 14), (33824, 481), (33825, 565), (37389, 203), (40695, 566),
  (42904, 60), (45868, 2856), (46500, 1), (47014, 62), (47038, 2854),
  (48377, 731), (48387, 2580), (48492, 360), (49328, 167), (50970, 4),
  (55017, 2579), (55583, 1565), (57600, 2), (57606, 101), (58574, 483),
  (58581, 1249)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X0Y0_check. -/
theorem X1Split78A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split78A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X0Y0_pairs. -/
theorem X1Split78A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks3S2048Chunk0 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split78A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S2048Chunk0 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split78A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X0_pairs. -/
theorem X1Split78A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split78A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split78A0X1Y0Certs : List (Nat × Nat) := [
  (1370, 1099), (1371, 1245), (4307, 724), (7204, 63), (9620, 1106),
  (11048, 163), (14715, 560), (16730, 1107), (18692, 27), (19149, 202),
  (19168, 2855), (19262, 29), (19988, 168), (19989, 205), (20529, 206),
  (22253, 1568), (22259, 3162), (22368, 834), (23564, 490), (31529, 3163),
  (32397, 2572), (35192, 26), (35202, 358), (35657, 726), (35791, 15),
  (35810, 1103), (38691, 1247), (39025, 2034), (41155, 2027), (43394, 485),
  (50640, 0), (50652, 359), (53093, 1569), (55924, 59), (55945, 2032),
  (57071, 300), (57599, 3161), (60156, 105), (60168, 837)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X1Y0_check. -/
theorem X1Split78A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split78A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X1Y0_pairs. -/
theorem X1Split78A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks1S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 4
    outerMasks3S2048Chunk1 masks1S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split78A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks1S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S2048Chunk1 masks1S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks1S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks1S512Chunk0_bound y hy)
  · exact X1Split78A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0X1_pairs. -/
theorem X1Split78A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks1S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks1S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split78A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78A0_pairs. -/
theorem X1Split78A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 1,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 4 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split78A0X0_pairs x hx y hy hw
  · exact X1Split78A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split78_check. -/
theorem X1Split78_check : checkSplit m4TX1 (3, 4, 1, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 1 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split78A0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split79A0X0Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X0Y0_check. -/
theorem X1Split79A0X0Y0_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split79A0X0Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X0Y0_pairs. -/
theorem X1Split79A0X0Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks3S2048Chunk0 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split79A0X0Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk0_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S2048Chunk0 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk0_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S2048Chunk0_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split79A0X0Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X0_pairs. -/
theorem X1Split79A0X0_pairs : ∀ x ∈ outerMasks3S2048Chunk0, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split79A0X0Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Grid-lane indices and census witnesses for every matching weight. -/
def X1Split79A0X1Y0Certs : List (Nat × Nat) := []

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X1Y0_check. -/
theorem X1Split79A0X1Y0_check : checkGrid m4TX1 censusX1 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split79A0X1Y0Certs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X1Y0_pairs. -/
theorem X1Split79A0X1Y0_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masks0S512Chunk0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  apply checkGrid_sound m4TX1 censusX1 0 0 5
    outerMasks3S2048Chunk1 masks0S512Chunk0
    (gridWords outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns) X1Split79A0X1Y0Certs
  · exact censusX1_valid
  · decide
  · decide
  · decide
  · exact outerMasks3S2048Chunk1_bound
  · exact masks0S512Chunk0_bound
  · intro x hx
    exact X1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
  · intro y hy
    exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · apply gridWords_eq m4TX1 0 outerMasks3S2048Chunk1 masks0S512Chunk0
      X1M0LeftColumns X1M0RightColumns
    · decide
    · exact outerMasks3S2048Chunk1_bound
    · exact masks0S512Chunk0_bound
    · intro z hz
      exact ⟨(X1M0Left_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Left_columns_bound z hz).2 (by decide)⟩
    · intro z hz
      exact ⟨(X1M0Right_columns_bound z hz).1,
        lt_of_lt_of_le (X1M0Right_columns_bound z hz).2 (by decide)⟩
    · exact X1M0Left_eq
    · exact X1M0Right_eq
    · intro x hx
      exact X1M0Left_bound x (outerMasks3S2048Chunk1_bound x hx)
    · intro y hy
      exact X1M0Right_bound y (masks0S512Chunk0_bound y hy)
  · exact X1Split79A0X1Y0_check

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0X1_pairs. -/
theorem X1Split79A0X1_pairs : ∀ x ∈ outerMasks3S2048Chunk1, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← masks0S512_cover] at hy
  obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
  simp only [masks0S512Chunks, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl
  · exact X1Split79A0X1Y0_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79A0_pairs. -/
theorem X1Split79A0_pairs : ∀ x ∈ masksOfWt 30 3, ∀ y ∈ masksOfWt 30 0,
    popCntGo 30 (sweepOutput m4TX1 0 x y 0) = 5 →
      sweepAccept m4TX1 0 x y 0 = true := by
  intro x hx y hy hw
  rw [← outerMasks3S2048_cover] at hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  simp only [outerMasks3S2048Chunks, List.mem_cons, List.not_mem_nil, or_false] at hxs
  rcases hxs with rfl | rfl
  · exact X1Split79A0X0_pairs x hx y hy hw
  · exact X1Split79A0X1_pairs x hx y hy hw

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1Split79_check. -/
theorem X1Split79_check : checkSplit m4TX1 (3, 5, 0, 0) = true := by
  apply checkSplit_of_pairs
  · intro x hx y hy a ha
    apply sweepOutput_lt
    · exact X1M0Left_bound x (masksOfWt_bound 30 3 x hx)
    · exact X1M0Right_bound y (masksOfWt_bound 30 0 y hy)
    · exact X1M0_ann_bound a ha
  · intro x hx y hy a ha hw
    have hann : a ∈ ([
  0
] : List Nat) := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hann
    rcases hann with rfl
    · exact X1Split79A0_pairs x hx y hy hw

end Quantum.Stabilizer.Homological.LP.M150

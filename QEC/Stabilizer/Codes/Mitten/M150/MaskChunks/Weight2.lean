/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.SweepAdapters
import QEC.Stabilizer.Codes.Mitten.M150.MaskEnumeration

namespace Quantum.Stabilizer.Homological.LP.M150
open F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def masks2S512Leaf0 : List Nat := [
  3, 5, 6, 9, 10, 12,
  17, 18, 20, 24, 33, 34,
  36, 40, 48, 65, 66, 68,
  72, 80, 96, 129, 130, 132,
  136, 144, 160, 192, 257, 258,
  260, 264, 272, 288, 320, 384,
  513, 514, 516, 520, 528, 544,
  576, 640, 768, 1025, 1026, 1028,
  1032, 1040, 1056, 1088, 1152, 1280,
  1536, 2049, 2050, 2052, 2056, 2064,
  2080, 2112, 2176, 2304, 2560, 3072,
  4097, 4098, 4100, 4104, 4112, 4128,
  4160, 4224, 4352, 4608, 5120, 6144,
  8193, 8194, 8196, 8200, 8208, 8224,
  8256, 8320, 8448, 8704, 9216, 10240,
  12288, 16385, 16386, 16388, 16392, 16400,
  16416, 16448, 16512, 16640, 16896, 17408,
  18432, 20480, 24576, 32769, 32770, 32772,
  32776, 32784, 32800, 32832, 32896, 33024,
  33280, 33792, 34816, 36864, 40960, 49152,
  65537, 65538, 65540, 65544, 65552, 65568,
  65600, 65664, 65792, 66048, 66560, 67584,
  69632, 73728, 81920, 98304, 131073, 131074,
  131076, 131080, 131088, 131104, 131136, 131200,
  131328, 131584, 132096, 133120, 135168, 139264,
  147456, 163840, 196608, 262145, 262146, 262148,
  262152, 262160, 262176, 262208, 262272, 262400,
  262656, 263168, 264192, 266240, 270336, 278528,
  294912, 327680, 393216, 524289, 524290, 524292,
  524296, 524304, 524320, 524352, 524416, 524544,
  524800, 525312, 526336, 528384, 532480, 540672,
  557056, 589824, 655360, 786432, 1048577, 1048578,
  1048580, 1048584, 1048592, 1048608, 1048640, 1048704,
  1048832, 1049088, 1049600, 1050624, 1052672, 1056768,
  1064960, 1081344, 1114112, 1179648, 1310720, 1572864,
  2097153, 2097154, 2097156, 2097160, 2097168, 2097184,
  2097216, 2097280, 2097408, 2097664, 2098176, 2099200,
  2101248, 2105344, 2113536, 2129920, 2162688, 2228224,
  2359296, 2621440, 3145728, 4194305, 4194306, 4194308,
  4194312, 4194320, 4194336, 4194368, 4194432, 4194560,
  4194816, 4195328, 4196352, 4198400, 4202496, 4210688,
  4227072, 4259840, 4325376, 4456448, 4718592, 5242880,
  6291456, 8388609, 8388610, 8388612, 8388616, 8388624,
  8388640, 8388672, 8388736, 8388864, 8389120, 8389632,
  8390656, 8392704, 8396800, 8404992, 8421376, 8454144,
  8519680, 8650752, 8912896, 9437184, 10485760, 12582912,
  16777217, 16777218, 16777220, 16777224, 16777232, 16777248,
  16777280, 16777344, 16777472, 16777728, 16778240, 16779264,
  16781312, 16785408, 16793600, 16809984, 16842752, 16908288,
  17039360, 17301504, 17825792, 18874368, 20971520, 25165824,
  33554433, 33554434, 33554436, 33554440, 33554448, 33554464,
  33554496, 33554560, 33554688, 33554944, 33555456, 33556480,
  33558528, 33562624, 33570816, 33587200, 33619968, 33685504,
  33816576, 34078720, 34603008, 35651584, 37748736, 41943040,
  50331648, 67108865, 67108866, 67108868, 67108872, 67108880,
  67108896, 67108928, 67108992, 67109120, 67109376, 67109888,
  67110912, 67112960, 67117056, 67125248, 67141632, 67174400,
  67239936, 67371008, 67633152, 68157440, 69206016, 71303168,
  75497472, 83886080, 100663296, 134217729, 134217730, 134217732,
  134217736, 134217744, 134217760, 134217792, 134217856, 134217984,
  134218240, 134218752, 134219776, 134221824, 134225920, 134234112,
  134250496, 134283264, 134348800, 134479872, 134742016, 135266304,
  136314880, 138412032, 142606336, 150994944, 167772160, 201326592,
  268435457, 268435458, 268435460, 268435464, 268435472, 268435488,
  268435520, 268435584, 268435712, 268435968, 268436480, 268437504,
  268439552, 268443648, 268451840, 268468224, 268500992, 268566528,
  268697600, 268959744, 269484032, 270532608, 272629760, 276824064,
  285212672, 301989888, 335544320, 402653184, 536870913, 536870914,
  536870916, 536870920, 536870928, 536870944, 536870976, 536871040,
  536871168, 536871424, 536871936, 536872960, 536875008, 536879104,
  536887296, 536903680, 536936448, 537001984, 537133056, 537395200,
  537919488, 538968064, 541065216, 545259520, 553648128, 570425344,
  603979776, 671088640, 805306368
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks2S512Leaf0_enumerates. -/
theorem masks2S512Leaf0_enumerates : masks2S512Leaf0 = (masksOfWt 30 2).map (fun m => m ||| 0) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def masks2S512Chunk0 : List Nat := masks2S512Leaf0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def masks2S512Chunks : List (List Nat) := [
  masks2S512Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def masks2S512Cover : MaskCover 30 2 0 := MaskCover.leaf masks2S512Leaf0
  masks2S512Leaf0_enumerates

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks2S512_cover. -/
theorem masks2S512_cover : masks2S512Chunks.flatten = masksOfWt 30 2 := by
  exact MaskCover.cover_zero masks2S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks2S512Chunk0_bound. -/
theorem masks2S512Chunk0_bound : ∀ x ∈ masks2S512Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 2 x
  rw [← masks2S512_cover]
  exact List.mem_flatten.mpr ⟨masks2S512Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def masks2S2048Chunk0 : List Nat := masks2S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def masks2S2048Chunks : List (List Nat) := [
  masks2S2048Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def masks2S2048Cover : MaskCover 30 2 0 := masks2S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks2S2048_cover. -/
theorem masks2S2048_cover : masks2S2048Chunks.flatten = masksOfWt 30 2 := by
  exact MaskCover.cover_zero masks2S2048Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for masks2S2048Chunk0_bound. -/
theorem masks2S2048Chunk0_bound : ∀ x ∈ masks2S2048Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 2 x
  rw [← masks2S2048_cover]
  exact List.mem_flatten.mpr ⟨masks2S2048Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf0 : List Nat := [
  3, 5, 6, 9, 10, 12,
  17, 18, 20, 24, 33, 34,
  36, 40, 48, 65, 66, 68,
  72, 80, 96, 129, 130, 132,
  136, 144, 160, 192, 257, 258,
  260, 264, 272, 288, 320, 384,
  513, 514, 516, 520, 528, 544,
  576, 640, 768, 1025, 1026, 1028,
  1032, 1040, 1056, 1088, 1152, 1280,
  1536, 2049, 2050, 2052, 2056, 2064,
  2080, 2112, 2176, 2304, 2560, 3072,
  4097, 4098, 4100, 4104, 4112, 4128,
  4160, 4224, 4352, 4608, 5120, 6144,
  8193, 8194, 8196, 8200, 8208, 8224,
  8256, 8320, 8448, 8704, 9216, 10240,
  12288, 16385, 16386, 16388, 16392, 16400,
  16416, 16448, 16512, 16640, 16896, 17408,
  18432, 20480, 24576, 32769, 32770, 32772,
  32776, 32784, 32800, 32832, 32896, 33024,
  33280, 33792, 34816, 36864, 40960, 49152,
  65537, 65538, 65540, 65544, 65552, 65568,
  65600, 65664, 65792, 66048, 66560, 67584,
  69632, 73728, 81920, 98304, 131073, 131074,
  131076, 131080, 131088, 131104, 131136, 131200,
  131328, 131584, 132096, 133120, 135168, 139264,
  147456, 163840, 196608, 262145, 262146, 262148,
  262152, 262160, 262176, 262208, 262272, 262400,
  262656, 263168, 264192, 266240, 270336, 278528,
  294912, 327680, 393216, 524289, 524290, 524292,
  524296, 524304, 524320, 524352, 524416, 524544,
  524800, 525312, 526336, 528384, 532480, 540672,
  557056, 589824, 655360, 786432, 1048577, 1048578,
  1048580, 1048584, 1048592, 1048608, 1048640, 1048704,
  1048832, 1049088, 1049600, 1050624, 1052672, 1056768,
  1064960, 1081344, 1114112, 1179648, 1310720, 1572864,
  2097153, 2097154, 2097156, 2097160, 2097168, 2097184,
  2097216, 2097280, 2097408, 2097664, 2098176, 2099200,
  2101248, 2105344, 2113536, 2129920, 2162688, 2228224,
  2359296, 2621440, 3145728, 4194305, 4194306, 4194308,
  4194312, 4194320, 4194336, 4194368, 4194432, 4194560,
  4194816, 4195328, 4196352, 4198400, 4202496, 4210688,
  4227072, 4259840, 4325376, 4456448, 4718592, 5242880,
  6291456
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf0_enumerates. -/
theorem outerMasks2S256Leaf0_enumerates :
    outerMasks2S256Leaf0 = (masksOfWt 23 2).map (fun m => m ||| 0) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf1 : List Nat := [
  8388609, 8388610, 8388612, 8388616, 8388624, 8388640,
  8388672, 8388736, 8388864, 8389120, 8389632, 8390656,
  8392704, 8396800, 8404992, 8421376, 8454144, 8519680,
  8650752, 8912896, 9437184, 10485760, 12582912
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf1_enumerates. -/
theorem outerMasks2S256Leaf1_enumerates :
    outerMasks2S256Leaf1 = (masksOfWt 23 1).map (fun m => m ||| 8388608) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf2 : List Nat := [
  16777217, 16777218, 16777220, 16777224, 16777232, 16777248,
  16777280, 16777344, 16777472, 16777728, 16778240, 16779264,
  16781312, 16785408, 16793600, 16809984, 16842752, 16908288,
  17039360, 17301504, 17825792, 18874368, 20971520, 25165824
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf2_enumerates. -/
theorem outerMasks2S256Leaf2_enumerates :
    outerMasks2S256Leaf2 = (masksOfWt 24 1).map (fun m => m ||| 16777216) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf3 : List Nat := [
  33554433, 33554434, 33554436, 33554440, 33554448, 33554464,
  33554496, 33554560, 33554688, 33554944, 33555456, 33556480,
  33558528, 33562624, 33570816, 33587200, 33619968, 33685504,
  33816576, 34078720, 34603008, 35651584, 37748736, 41943040,
  50331648
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf3_enumerates. -/
theorem outerMasks2S256Leaf3_enumerates :
    outerMasks2S256Leaf3 = (masksOfWt 25 1).map (fun m => m ||| 33554432) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf4 : List Nat := [
  67108865, 67108866, 67108868, 67108872, 67108880, 67108896,
  67108928, 67108992, 67109120, 67109376, 67109888, 67110912,
  67112960, 67117056, 67125248, 67141632, 67174400, 67239936,
  67371008, 67633152, 68157440, 69206016, 71303168, 75497472,
  83886080, 100663296
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf4_enumerates. -/
theorem outerMasks2S256Leaf4_enumerates :
    outerMasks2S256Leaf4 = (masksOfWt 26 1).map (fun m => m ||| 67108864) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf5 : List Nat := [
  134217729, 134217730, 134217732, 134217736, 134217744, 134217760,
  134217792, 134217856, 134217984, 134218240, 134218752, 134219776,
  134221824, 134225920, 134234112, 134250496, 134283264, 134348800,
  134479872, 134742016, 135266304, 136314880, 138412032, 142606336,
  150994944, 167772160, 201326592
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf5_enumerates. -/
theorem outerMasks2S256Leaf5_enumerates :
    outerMasks2S256Leaf5 = (masksOfWt 27 1).map (fun m => m ||| 134217728) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf6 : List Nat := [
  268435457, 268435458, 268435460, 268435464, 268435472, 268435488,
  268435520, 268435584, 268435712, 268435968, 268436480, 268437504,
  268439552, 268443648, 268451840, 268468224, 268500992, 268566528,
  268697600, 268959744, 269484032, 270532608, 272629760, 276824064,
  285212672, 301989888, 335544320, 402653184
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf6_enumerates. -/
theorem outerMasks2S256Leaf6_enumerates :
    outerMasks2S256Leaf6 = (masksOfWt 28 1).map (fun m => m ||| 268435456) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- One bounded leaf of the recursive fixed-weight mask enumeration. -/
def outerMasks2S256Leaf7 : List Nat := [
  536870913, 536870914, 536870916, 536870920, 536870928, 536870944,
  536870976, 536871040, 536871168, 536871424, 536871936, 536872960,
  536875008, 536879104, 536887296, 536903680, 536936448, 537001984,
  537133056, 537395200, 537919488, 538968064, 541065216, 545259520,
  553648128, 570425344, 603979776, 671088640, 805306368
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Leaf7_enumerates. -/
theorem outerMasks2S256Leaf7_enumerates :
    outerMasks2S256Leaf7 = (masksOfWt 29 1).map (fun m => m ||| 536870912) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks2S256Chunk0 : List Nat := outerMasks2S256Leaf0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks2S256Chunk1 : List Nat := outerMasks2S256Leaf1 ++
  outerMasks2S256Leaf2 ++
  outerMasks2S256Leaf3 ++
  outerMasks2S256Leaf4 ++
  outerMasks2S256Leaf5 ++
  outerMasks2S256Leaf6 ++
  outerMasks2S256Leaf7

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def outerMasks2S256Chunks : List (List Nat) := [
  outerMasks2S256Chunk0, outerMasks2S256Chunk1
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def outerMasks2S256Cover : MaskCover 30 2 0 := MaskCover.split
  (MaskCover.split
    (MaskCover.split
      (MaskCover.split
        (MaskCover.split
          (MaskCover.split
            (MaskCover.split
              (MaskCover.leaf outerMasks2S256Leaf0
                outerMasks2S256Leaf0_enumerates)
              (MaskCover.leaf outerMasks2S256Leaf1
                outerMasks2S256Leaf1_enumerates))
            (MaskCover.leaf outerMasks2S256Leaf2
              outerMasks2S256Leaf2_enumerates))
          (MaskCover.leaf outerMasks2S256Leaf3
            outerMasks2S256Leaf3_enumerates))
        (MaskCover.leaf outerMasks2S256Leaf4
          outerMasks2S256Leaf4_enumerates))
      (MaskCover.leaf outerMasks2S256Leaf5
        outerMasks2S256Leaf5_enumerates))
    (MaskCover.leaf outerMasks2S256Leaf6
      outerMasks2S256Leaf6_enumerates))
  (MaskCover.leaf outerMasks2S256Leaf7
    outerMasks2S256Leaf7_enumerates)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256_cover. -/
theorem outerMasks2S256_cover : outerMasks2S256Chunks.flatten = masksOfWt 30 2 := by
  exact MaskCover.cover_zero outerMasks2S256Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Chunk0_bound. -/
theorem outerMasks2S256Chunk0_bound : ∀ x ∈ outerMasks2S256Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 2 x
  rw [← outerMasks2S256_cover]
  exact List.mem_flatten.mpr ⟨outerMasks2S256Chunk0,
    List.mem_cons_self, hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S256Chunk1_bound. -/
theorem outerMasks2S256Chunk1_bound : ∀ x ∈ outerMasks2S256Chunk1, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 2 x
  rw [← outerMasks2S256_cover]
  exact List.mem_flatten.mpr ⟨outerMasks2S256Chunk1,
    List.mem_cons_of_mem _ (
      List.mem_cons_self), hx⟩

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- An ascending block of fixed-weight thirty-bit masks. -/
def outerMasks2S2048Chunk0 : List Nat := masks2S512Chunk0

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Blocks covering all masks of the specified weight. -/
def outerMasks2S2048Chunks : List (List Nat) := [
  outerMasks2S2048Chunk0
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- A recursive certificate combining the bounded enumeration leaves. -/
def outerMasks2S2048Cover : MaskCover 30 2 0 := masks2S512Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S2048_cover. -/
theorem outerMasks2S2048_cover : outerMasks2S2048Chunks.flatten = masksOfWt 30 2 := by
  exact MaskCover.cover_zero outerMasks2S2048Cover

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for outerMasks2S2048Chunk0_bound. -/
theorem outerMasks2S2048Chunk0_bound : ∀ x ∈ outerMasks2S2048Chunk0, x < 2 ^ 30 := by
  intro x hx
  apply masksOfWt_bound 30 2 x
  rw [← outerMasks2S2048_cover]
  exact List.mem_flatten.mpr ⟨outerMasks2S2048Chunk0,
    List.mem_cons_self, hx⟩

end Quantum.Stabilizer.Homological.LP.M150

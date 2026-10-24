/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_affine_boundaries.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart0
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census0 : (AffineBoundaryCached.cert0).seeds.map Prod.fst = AffineSearchData.allowed0 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 0 is a boundary. -/
theorem boundary0 : TopFiberBoundary 0xfc01c0000000000000000000000000000e00000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0000000000000000000000000000e00000000000)/2 = 5 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete0 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert0).beta ∈
      (AffineBoundaryCached.cert0).seeds.map Prod.fst := by
    rw [census0]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert0) 180 512
    32 AffineBoundaryCached.sheets0 AffineBoundaryCached.shadows0
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt0
    (AffineBoundaryCached.checked0) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census1 : (AffineBoundaryCached.cert1).seeds.map Prod.fst = AffineSearchData.allowed1 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 1 is a boundary. -/
theorem boundary1 : TopFiberBoundary 0x1200200000000000fc01c0000008000001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000000fc01c0000008000001000000000)/2 = 4 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete1 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert1).beta ∈
      (AffineBoundaryCached.cert1).seeds.map Prod.fst := by
    rw [census1]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert1) 180 512
    16 AffineBoundaryCached.sheets1 AffineBoundaryCached.shadows1
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt1
    (AffineBoundaryCached.checked1) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census2 : (AffineBoundaryCached.cert2).seeds.map Prod.fst = AffineSearchData.allowed2 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 2 is a boundary. -/
theorem boundary2 : TopFiberBoundary 0x3b80780000000000000000000060000003c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3b80780000000000000000000060000003c0000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete2 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert2).beta ∈
      (AffineBoundaryCached.cert2).seeds.map Prod.fst := by
    rw [census2]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert2) 180 512
    14 AffineBoundaryCached.sheets2 AffineBoundaryCached.shadows2
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt2
    (AffineBoundaryCached.checked2) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census3 : (AffineBoundaryCached.cert3).seeds.map Prod.fst = AffineSearchData.allowed3 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 3 is a boundary. -/
theorem boundary3 : TopFiberBoundary 0xee01e0000000000000000000000600000f00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xee01e0000000000000000000000600000f00000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete3 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert3).beta ∈
      (AffineBoundaryCached.cert3).seeds.map Prod.fst := by
    rw [census3]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert3) 180 512
    14 AffineBoundaryCached.sheets3 AffineBoundaryCached.shadows3
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt3
    (AffineBoundaryCached.checked3) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census5 : (AffineBoundaryCached.cert5).seeds.map Prod.fst = AffineSearchData.allowed5 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 5 is a boundary. -/
theorem boundary5 : TopFiberBoundary 0x481f0038000000000000000000c000000401c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x481f0038000000000000000000c000000401c0000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete5 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert5).beta ∈
      (AffineBoundaryCached.cert5).seeds.map Prod.fst := by
    rw [census5]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert5) 180 512
    14 AffineBoundaryCached.sheets5 AffineBoundaryCached.shadows5
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt5
    (AffineBoundaryCached.checked5) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census6 : (AffineBoundaryCached.cert6).seeds.map Prod.fst = AffineSearchData.allowed6 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 6 is a boundary. -/
theorem boundary6 : TopFiberBoundary 0x1f8070008000000000000000000000c001c0040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f8070008000000000000000000000c001c0040000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete6 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert6).beta ∈
      (AffineBoundaryCached.cert6).seeds.map Prod.fst := by
    rw [census6]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert6) 180 512
    14 AffineBoundaryCached.sheets6 AffineBoundaryCached.shadows6
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt6
    (AffineBoundaryCached.checked6) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census7 : (AffineBoundaryCached.cert7).seeds.map Prod.fst = AffineSearchData.allowed7 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 7 is a boundary. -/
theorem boundary7 : TopFiberBoundary 0x2000000000006c0088070028001001000000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000006c0088070028001001000000003000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete7 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert7).beta ∈
      (AffineBoundaryCached.cert7).seeds.map Prod.fst := by
    rw [census7]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert7) 180 512
    16 AffineBoundaryCached.sheets7 AffineBoundaryCached.shadows7
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt7
    (AffineBoundaryCached.checked7) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census8 : (AffineBoundaryCached.cert8).seeds.map Prod.fst = AffineSearchData.allowed8 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 8 is a boundary. -/
theorem boundary8 : TopFiberBoundary 0x200000000000fc0188070008001001000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000fc0188070008001001000000000000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete8 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert8).beta ∈
      (AffineBoundaryCached.cert8).seeds.map Prod.fst := by
    rw [census8]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert8) 180 512
    16 AffineBoundaryCached.sheets8 AffineBoundaryCached.shadows8
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt8
    (AffineBoundaryCached.checked8) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census9 : (AffineBoundaryCached.cert9).seeds.map Prod.fst = AffineSearchData.allowed9 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 9 is a boundary. -/
theorem boundary9 : TopFiberBoundary 0x2002000000000006c0280180028008001000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000006c0280180028008001000000003)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete9 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert9).beta ∈
      (AffineBoundaryCached.cert9).seeds.map Prod.fst := by
    rw [census9]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert9) 180 512
    16 AffineBoundaryCached.sheets9 AffineBoundaryCached.shadows9
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt9
    (AffineBoundaryCached.checked9) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census10 : (AffineBoundaryCached.cert10).seeds.map Prod.fst = AffineSearchData.allowed10 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 10 is a boundary. -/
theorem boundary10 : TopFiberBoundary 0x200200000000000fc0380180008008001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000000fc0380180008008001000000000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete10 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert10).beta ∈
      (AffineBoundaryCached.cert10).seeds.map Prod.fst := by
    rw [census10]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert10) 180 512
    16 AffineBoundaryCached.sheets10 AffineBoundaryCached.shadows10
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt10
    (AffineBoundaryCached.checked10) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census11 : (AffineBoundaryCached.cert11).seeds.map Prod.fst = AffineSearchData.allowed11 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 11 is a boundary. -/
theorem boundary11 : TopFiberBoundary 0x205800a00000000000240180030020001005000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x205800a00000000000240180030020001005000000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete11 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert11).beta ∈
      (AffineBoundaryCached.cert11).seeds.map Prod.fst := by
    rw [census11]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert11) 180 512
    16 AffineBoundaryCached.sheets11 AffineBoundaryCached.shadows11
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt11
    (AffineBoundaryCached.checked11) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census12 : (AffineBoundaryCached.cert12).seeds.map Prod.fst = AffineSearchData.allowed12 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 12 is a boundary. -/
theorem boundary12 : TopFiberBoundary 0x2401b80380000000000000000060000002001c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2401b80380000000000000000060000002001c0000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete12 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert12).beta ∈
      (AffineBoundaryCached.cert12).seeds.map Prod.fst := by
    rw [census12]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert12) 180 512
    14 AffineBoundaryCached.sheets12 AffineBoundaryCached.shadows12
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt12
    (AffineBoundaryCached.checked12) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census13 : (AffineBoundaryCached.cert13).seeds.map Prod.fst = AffineSearchData.allowed13 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 13 is a boundary. -/
theorem boundary13 : TopFiberBoundary 0x2c00c00000000000900a8028001002000600000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c00c00000000000900a8028001002000600000000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete13 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert13).beta ∈
      (AffineBoundaryCached.cert13).seeds.map Prod.fst := by
    rw [census13]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert13) 180 512
    16 AffineBoundaryCached.sheets13 AffineBoundaryCached.shadows13
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt13
    (AffineBoundaryCached.checked13) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census15 : (AffineBoundaryCached.cert15).seeds.map Prod.fst = AffineSearchData.allowed15 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 15 is a boundary. -/
theorem boundary15 : TopFiberBoundary 0xfc00e0020000000000000000000000600e00100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc00e0020000000000000000000000600e00100000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete15 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert15).beta ∈
      (AffineBoundaryCached.cert15).seeds.map Prod.fst := by
    rw [census15]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert15) 180 512
    14 AffineBoundaryCached.sheets15 AffineBoundaryCached.shadows15
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt15
    (AffineBoundaryCached.checked15) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census16 : (AffineBoundaryCached.cert16).seeds.map Prod.fst = AffineSearchData.allowed16 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 16 is a boundary. -/
theorem boundary16 : TopFiberBoundary 0x10000000000024002c0280100018008000000028003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000024002c0280100018008000000028003)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete16 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert16).beta ∈
      (AffineBoundaryCached.cert16).seeds.map Prod.fst := by
    rw [census16]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert16) 180 512
    16 AffineBoundaryCached.sheets16 AffineBoundaryCached.shadows16
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt16
    (AffineBoundaryCached.checked16) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census17 : (AffineBoundaryCached.cert17).seeds.map Prod.fst = AffineSearchData.allowed17 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 17 is a boundary. -/
theorem boundary17 : TopFiberBoundary 0x10000000000024032004401000c0008000000028018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000024032004401000c0008000000028018)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete17 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert17).beta ∈
      (AffineBoundaryCached.cert17).seeds.map Prod.fst := by
    rw [census17]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert17) 180 512
    16 AffineBoundaryCached.sheets17 AffineBoundaryCached.shadows17
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt17
    (AffineBoundaryCached.checked17) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census20 : (AffineBoundaryCached.cert20).seeds.map Prod.fst = AffineSearchData.allowed20 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 20 is a boundary. -/
theorem boundary20 : TopFiberBoundary 0x30036006000000000006c00c0000000000003000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000000000006c00c0000000000003000000)/2 = 3 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete20 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert20).beta ∈
      (AffineBoundaryCached.cert20).seeds.map Prod.fst := by
    rw [census20]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert20) 180 512
    18 AffineBoundaryCached.sheets20 AffineBoundaryCached.shadows20
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt20
    (AffineBoundaryCached.checked20) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census21 : (AffineBoundaryCached.cert21).seeds.map Prod.fst = AffineSearchData.allowed21 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 21 is a boundary. -/
theorem boundary21 : TopFiberBoundary 0x1f80380000009001000000200000000001c0003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f80380000009001000000200000000001c0003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete21 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert21).beta ∈
      (AffineBoundaryCached.cert21).seeds.map Prod.fst := by
    rw [census21]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert21) 180 512
    12 AffineBoundaryCached.sheets21 AffineBoundaryCached.shadows21
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt21
    (AffineBoundaryCached.checked21) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census22 : (AffineBoundaryCached.cert22).seeds.map Prod.fst = AffineSearchData.allowed22 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 22 is a boundary. -/
theorem boundary22 : TopFiberBoundary 0x240040000000fc01c0000038006000000200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x240040000000fc01c0000038006000000200000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete22 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert22).beta ∈
      (AffineBoundaryCached.cert22).seeds.map Prod.fst := by
    rw [census22]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert22) 180 512
    12 AffineBoundaryCached.sheets22 AffineBoundaryCached.shadows22
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt22
    (AffineBoundaryCached.checked22) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census23 : (AffineBoundaryCached.cert23).seeds.map Prod.fst = AffineSearchData.allowed23 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 23 is a boundary. -/
theorem boundary23 : TopFiberBoundary 0x7380f80000000000000000000030000007c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7380f80000000000000000000030000007c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete23 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert23).beta ∈
      (AffineBoundaryCached.cert23).seeds.map Prod.fst := by
    rw [census23]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert23) 180 512
    10 AffineBoundaryCached.sheets23 AffineBoundaryCached.shadows23
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt23
    (AffineBoundaryCached.checked23) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census24 : (AffineBoundaryCached.cert24).seeds.map Prod.fst = AffineSearchData.allowed24 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 24 is a boundary. -/
theorem boundary24 : TopFiberBoundary 0xe381f8000000000000000000000000000fc0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe381f8000000000000000000000000000fc0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete24 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert24).beta ∈
      (AffineBoundaryCached.cert24).seeds.map Prod.fst := by
    rw [census24]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert24) 180 512
    6 AffineBoundaryCached.sheets24 AffineBoundaryCached.shadows24
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt24
    (AffineBoundaryCached.checked24) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census25 : (AffineBoundaryCached.cert25).seeds.map Prod.fst = AffineSearchData.allowed25 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 25 is a boundary. -/
theorem boundary25 : TopFiberBoundary 0xe701f0000000000000000000000c00000f80000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe701f0000000000000000000000c00000f80000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete25 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert25).beta ∈
      (AffineBoundaryCached.cert25).seeds.map Prod.fst := by
    rw [census25]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert25) 180 512
    10 AffineBoundaryCached.sheets25 AffineBoundaryCached.shadows25
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt25
    (AffineBoundaryCached.checked25) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census26 : (AffineBoundaryCached.cert26).seeds.map Prod.fst = AffineSearchData.allowed26 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 26 is a boundary. -/
theorem boundary26 : TopFiberBoundary 0xfc01c0000000900100000020000000000e00003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0000000900100000020000000000e00003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete26 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert26).beta ∈
      (AffineBoundaryCached.cert26).seeds.map Prod.fst := by
    rw [census26]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert26) 180 512
    12 AffineBoundaryCached.sheets26 AffineBoundaryCached.shadows26
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt26
    (AffineBoundaryCached.checked26) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census27 : (AffineBoundaryCached.cert27).seeds.map Prod.fst = AffineSearchData.allowed27 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 27 is a boundary. -/
theorem boundary27 : TopFiberBoundary 0x1200200000000fc01c0000038030000001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000fc01c0000038030000001000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete27 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert27).beta ∈
      (AffineBoundaryCached.cert27).seeds.map Prod.fst := by
    rw [census27]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert27) 180 512
    12 AffineBoundaryCached.sheets27 AffineBoundaryCached.shadows27
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt27
    (AffineBoundaryCached.checked27) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census28 : (AffineBoundaryCached.cert28).seeds.map Prod.fst = AffineSearchData.allowed28 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 28 is a boundary. -/
theorem boundary28 : TopFiberBoundary 0x13f82380000000000000000000300000011c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x13f82380000000000000000000300000011c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete28 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert28).beta ∈
      (AffineBoundaryCached.cert28).seeds.map Prod.fst := by
    rw [census28]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert28) 180 512
    12 AffineBoundaryCached.sheets28 AffineBoundaryCached.shadows28
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt28
    (AffineBoundaryCached.checked28) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census29 : (AffineBoundaryCached.cert29).seeds.map Prod.fst = AffineSearchData.allowed29 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 29 is a boundary. -/
theorem boundary29 : TopFiberBoundary 0x1600600000000002080b40140088010003000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1600600000000002080b40140088010003000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete29 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert29).beta ∈
      (AffineBoundaryCached.cert29).seeds.map Prod.fst := by
    rw [census29]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert29) 180 512
    10 AffineBoundaryCached.sheets29 AffineBoundaryCached.shadows29
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt29
    (AffineBoundaryCached.checked29) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census30 : (AffineBoundaryCached.cert30).seeds.map Prod.fst = AffineSearchData.allowed30 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 30 is a boundary. -/
theorem boundary30 : TopFiberBoundary 0x7e00e00000000240040000008000000007000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7e00e00000000240040000008000000007000006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete30 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert30).beta ∈
      (AffineBoundaryCached.cert30).seeds.map Prod.fst := by
    rw [census30]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert30) 180 512
    12 AffineBoundaryCached.sheets30 AffineBoundaryCached.shadows30
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt30
    (AffineBoundaryCached.checked30) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census31 : (AffineBoundaryCached.cert31).seeds.map Prod.fst = AffineSearchData.allowed31 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 31 is a boundary. -/
theorem boundary31 : TopFiberBoundary 0x7e48e08000000000000000000000c00007040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7e48e08000000000000000000000c00007040000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete31 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert31).beta ∈
      (AffineBoundaryCached.cert31).seeds.map Prod.fst := by
    rw [census31]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert31) 180 512
    12 AffineBoundaryCached.sheets31 AffineBoundaryCached.shadows31
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt31
    (AffineBoundaryCached.checked31) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census32 : (AffineBoundaryCached.cert32).seeds.map Prod.fst = AffineSearchData.allowed32 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 32 is a boundary. -/
theorem boundary32 : TopFiberBoundary 0x9001000000000fc01c0000038180000008000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x9001000000000fc01c0000038180000008000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete32 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert32).beta ∈
      (AffineBoundaryCached.cert32).seeds.map Prod.fst := by
    rw [census32]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert32) 180 512
    12 AffineBoundaryCached.sheets32 AffineBoundaryCached.shadows32
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt32
    (AffineBoundaryCached.checked32) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census33 : (AffineBoundaryCached.cert33).seeds.map Prod.fst = AffineSearchData.allowed33 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 33 is a boundary. -/
theorem boundary33 : TopFiberBoundary 0x91f90380000000000000000001800000081c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x91f90380000000000000000001800000081c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete33 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert33).beta ∈
      (AffineBoundaryCached.cert33).seeds.map Prod.fst := by
    rw [census33]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert33) 180 512
    12 AffineBoundaryCached.sheets33 AffineBoundaryCached.shadows33
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt33
    (AffineBoundaryCached.checked33) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census34 : (AffineBoundaryCached.cert34).seeds.map Prod.fst = AffineSearchData.allowed34 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 34 is a boundary. -/
theorem boundary34 : TopFiberBoundary 0x19003000000000002080b40140050010018000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x19003000000000002080b40140050010018000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete34 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert34).beta ∈
      (AffineBoundaryCached.cert34).seeds.map Prod.fst := by
    rw [census34]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert34) 180 512
    10 AffineBoundaryCached.sheets34 AffineBoundaryCached.shadows34
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt34
    (AffineBoundaryCached.checked34) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census35 : (AffineBoundaryCached.cert35).seeds.map Prod.fst = AffineSearchData.allowed35 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 35 is a boundary. -/
theorem boundary35 : TopFiberBoundary 0x3f007000000000240040000008000000038000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3f007000000000240040000008000000038000006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete35 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert35).beta ∈
      (AffineBoundaryCached.cert35).seeds.map Prod.fst := by
    rw [census35]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert35) 180 512
    12 AffineBoundaryCached.sheets35 AffineBoundaryCached.shadows35
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt35
    (AffineBoundaryCached.checked35) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census36 : (AffineBoundaryCached.cert36).seeds.map Prod.fst = AffineSearchData.allowed36 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 36 is a boundary. -/
theorem boundary36 : TopFiberBoundary 0x3f04f008000000000000000000000c00038040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3f04f008000000000000000000000c00038040000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete36 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert36).beta ∈
      (AffineBoundaryCached.cert36).seeds.map Prod.fst := by
    rw [census36]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert36) 180 512
    12 AffineBoundaryCached.sheets36 AffineBoundaryCached.shadows36
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt36
    (AffineBoundaryCached.checked36) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census37 : (AffineBoundaryCached.cert37).seeds.map Prod.fst = AffineSearchData.allowed37 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 37 is a boundary. -/
theorem boundary37 : TopFiberBoundary 0x48008000000000fc01c0000038c00000040000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x48008000000000fc01c0000038c00000040000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete37 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert37).beta ∈
      (AffineBoundaryCached.cert37).seeds.map Prod.fst := by
    rw [census37]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert37) 180 512
    12 AffineBoundaryCached.sheets37 AffineBoundaryCached.shadows37
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt37
    (AffineBoundaryCached.checked37) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census38 : (AffineBoundaryCached.cert38).seeds.map Prod.fst = AffineSearchData.allowed38 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 38 is a boundary. -/
theorem boundary38 : TopFiberBoundary 0xc00c00000000000d80d8018000003000600000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xc00c00000000000d80d8018000003000600000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete38 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert38).beta ∈
      (AffineBoundaryCached.cert38).seeds.map Prod.fst := by
    rw [census38]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert38) 180 512
    6 AffineBoundaryCached.sheets38 AffineBoundaryCached.shadows38
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt38
    (AffineBoundaryCached.checked38) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census39 : (AffineBoundaryCached.cert39).seeds.map Prod.fst = AffineSearchData.allowed39 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 39 is a boundary. -/
theorem boundary39 : TopFiberBoundary 0xd81e00380000000000000000006000000c01c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xd81e00380000000000000000006000000c01c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete39 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert39).beta ∈
      (AffineBoundaryCached.cert39).seeds.map Prod.fst := by
    rw [census39]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert39) 180 512
    10 AffineBoundaryCached.sheets39 AffineBoundaryCached.shadows39
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt39
    (AffineBoundaryCached.checked39) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census40 : (AffineBoundaryCached.cert40).seeds.map Prod.fst = AffineSearchData.allowed40 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 40 is a boundary. -/
theorem boundary40 : TopFiberBoundary 0x1f80380000000002400400000080000001c0000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f80380000000002400400000080000001c0000006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete40 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert40).beta ∈
      (AffineBoundaryCached.cert40).seeds.map Prod.fst := by
    rw [census40]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert40) 180 512
    12 AffineBoundaryCached.sheets40 AffineBoundaryCached.shadows40
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt40
    (AffineBoundaryCached.checked40) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census41 : (AffineBoundaryCached.cert41).seeds.map Prod.fst = AffineSearchData.allowed41 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 41 is a boundary. -/
theorem boundary41 : TopFiberBoundary 0x1f80e00180000000000000000000006001c00c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f80e00180000000000000000000006001c00c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete41 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert41).beta ∈
      (AffineBoundaryCached.cert41).seeds.map Prod.fst := by
    rw [census41]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert41) 180 512
    10 AffineBoundaryCached.sheets41 AffineBoundaryCached.shadows41
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt41
    (AffineBoundaryCached.checked41) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census42 : (AffineBoundaryCached.cert42).seeds.map Prod.fst = AffineSearchData.allowed42 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 42 is a boundary. -/
theorem boundary42 : TopFiberBoundary 0x1f81c00380000000000000000000000001c01c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f81c00380000000000000000000000001c01c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete42 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert42).beta ∈
      (AffineBoundaryCached.cert42).seeds.map Prod.fst := by
    rw [census42]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert42) 180 512
    6 AffineBoundaryCached.sheets42 AffineBoundaryCached.shadows42
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt42
    (AffineBoundaryCached.checked42) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census43 : (AffineBoundaryCached.cert43).seeds.map Prod.fst = AffineSearchData.allowed43 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 43 is a boundary. -/
theorem boundary43 : TopFiberBoundary 0x200000000000000f881b0030039001000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000000f881b0030039001000000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete43 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert43).beta ∈
      (AffineBoundaryCached.cert43).seeds.map Prod.fst := by
    rw [census43]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert43) 180 512
    6 AffineBoundaryCached.sheets43 AffineBoundaryCached.shadows43
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt43
    (AffineBoundaryCached.checked43) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census44 : (AffineBoundaryCached.cert44).seeds.map Prod.fst = AffineSearchData.allowed44 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 44 is a boundary. -/
theorem boundary44 : TopFiberBoundary 0x2000000000004806080b0020019001000000005003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000004806080b0020019001000000005003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete44 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert44).beta ∈
      (AffineBoundaryCached.cert44).seeds.map Prod.fst := by
    rw [census44]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert44) 180 512
    10 AffineBoundaryCached.sheets44 AffineBoundaryCached.shadows44
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt44
    (AffineBoundaryCached.checked44) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census45 : (AffineBoundaryCached.cert45).seeds.map Prod.fst = AffineSearchData.allowed45 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 45 is a boundary. -/
theorem boundary45 : TopFiberBoundary 0x200000000000688080070029001001000000003c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000688080070029001001000000003c00)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete45 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert45).beta ∈
      (AffineBoundaryCached.cert45).seeds.map Prod.fst := by
    rw [census45]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert45) 180 512
    10 AffineBoundaryCached.sheets45 AffineBoundaryCached.shadows45
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt45
    (AffineBoundaryCached.checked45) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census46 : (AffineBoundaryCached.cert46).seeds.map Prod.fst = AffineSearchData.allowed46 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 46 is a boundary. -/
theorem boundary46 : TopFiberBoundary 0x200000000000f88180070009001001000000000c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000f88180070009001001000000000c00)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete46 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert46).beta ∈
      (AffineBoundaryCached.cert46).seeds.map Prod.fst := by
    rw [census46]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert46) 180 512
    6 AffineBoundaryCached.sheets46 AffineBoundaryCached.shadows46
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt46
    (AffineBoundaryCached.checked46) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census47 : (AffineBoundaryCached.cert47).seeds.map Prod.fst = AffineSearchData.allowed47 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 47 is a boundary. -/
theorem boundary47 : TopFiberBoundary 0x2002000000000014c0080180068008001000000033 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000014c0080180068008001000000033)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete47 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert47).beta ∈
      (AffineBoundaryCached.cert47).seeds.map Prod.fst := by
    rw [census47]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert47) 180 512
    10 AffineBoundaryCached.sheets47 AffineBoundaryCached.shadows47
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt47
    (AffineBoundaryCached.checked47) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census48 : (AffineBoundaryCached.cert48).seeds.map Prod.fst = AffineSearchData.allowed48 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 48 is a boundary. -/
theorem boundary48 : TopFiberBoundary 0x200200000000001dc0180180048008001000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000001dc0180180048008001000000030)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete48 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert48).beta ∈
      (AffineBoundaryCached.cert48).seeds.map Prod.fst := by
    rw [census48]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert48) 180 512
    6 AffineBoundaryCached.sheets48 AffineBoundaryCached.shadows48
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt48
    (AffineBoundaryCached.checked48) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census49 : (AffineBoundaryCached.cert49).seeds.map Prod.fst = AffineSearchData.allowed49 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 49 is a boundary. -/
theorem boundary49 : TopFiberBoundary 0x2081b0038000000000000000006c000002401c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2081b0038000000000000000006c000002401c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete49 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert49).beta ∈
      (AffineBoundaryCached.cert49).seeds.map Prod.fst := by
    rw [census49]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert49) 180 512
    6 AffineBoundaryCached.sheets49 AffineBoundaryCached.shadows49
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt49
    (AffineBoundaryCached.checked49) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census50 : (AffineBoundaryCached.cert50).seeds.map Prod.fst = AffineSearchData.allowed50 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 50 is a boundary. -/
theorem boundary50 : TopFiberBoundary 0x240040000000000fc01c000003e000000200000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x240040000000000fc01c000003e000000200000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete50 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert50).beta ∈
      (AffineBoundaryCached.cert50).seeds.map Prod.fst := by
    rw [census50]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert50) 180 512
    12 AffineBoundaryCached.sheets50 AffineBoundaryCached.shadows50
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt50
    (AffineBoundaryCached.checked50) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census51 : (AffineBoundaryCached.cert51).seeds.map Prod.fst = AffineSearchData.allowed51 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 51 is a boundary. -/
theorem boundary51 : TopFiberBoundary 0x2c02800400000000900a8028001004000600200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2c02800400000000900a8028001004000600200000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete51 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert51).beta ∈
      (AffineBoundaryCached.cert51).seeds.map Prod.fst := by
    rw [census51]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert51) 180 512
    12 AffineBoundaryCached.sheets51 AffineBoundaryCached.shadows51
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt51
    (AffineBoundaryCached.checked51) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census52 : (AffineBoundaryCached.cert52).seeds.map Prod.fst = AffineSearchData.allowed52 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 52 is a boundary. -/
theorem boundary52 : TopFiberBoundary 0x300100000000000168168028006005000800000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300100000000000168168028006005000800000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete52 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert52).beta ∈
      (AffineBoundaryCached.cert52).seeds.map Prod.fst := by
    rw [census52]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert52) 180 512
    12 AffineBoundaryCached.sheets52 AffineBoundaryCached.shadows52
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt52
    (AffineBoundaryCached.checked52) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census53 : (AffineBoundaryCached.cert53).seeds.map Prod.fst = AffineSearchData.allowed53 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 53 is a boundary. -/
theorem boundary53 : TopFiberBoundary 0x3b8030008000000000000000006000c003c0040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3b8030008000000000000000006000c003c0040000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete53 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert53).beta ∈
      (AffineBoundaryCached.cert53).seeds.map Prod.fst := by
    rw [census53]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert53) 180 512
    6 AffineBoundaryCached.sheets53 AffineBoundaryCached.shadows53
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt53
    (AffineBoundaryCached.checked53) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census54 : (AffineBoundaryCached.cert54).seeds.map Prod.fst = AffineSearchData.allowed54 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 54 is a boundary. -/
theorem boundary54 : TopFiberBoundary 0x400400000001200dc0540100010010002000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x400400000001200dc0540100010010002000030000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete54 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert54).beta ∈
      (AffineBoundaryCached.cert54).seeds.map Prod.fst := by
    rw [census54]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert54) 180 512
    6 AffineBoundaryCached.sheets54 AffineBoundaryCached.shadows54
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt54
    (AffineBoundaryCached.checked54) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census55 : (AffineBoundaryCached.cert55).seeds.map Prod.fst = AffineSearchData.allowed55 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 55 is a boundary. -/
theorem boundary55 : TopFiberBoundary 0x480058050001001000000200005000600800140040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x480058050001001000000200005000600800140040)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete55 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert55).beta ∈
      (AffineBoundaryCached.cert55).seeds.map Prod.fst := by
    rw [census55]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert55) 180 512
    12 AffineBoundaryCached.sheets55 AffineBoundaryCached.shadows55
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt55
    (AffineBoundaryCached.checked55) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census56 : (AffineBoundaryCached.cert56).seeds.map Prod.fst = AffineSearchData.allowed56 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 56 is a boundary. -/
theorem boundary56 : TopFiberBoundary 0x480178070001001000000200005000000800040040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x480178070001001000000200005000000800040040)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete56 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert56).beta ∈
      (AffineBoundaryCached.cert56).seeds.map Prod.fst := by
    rw [census56]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert56) 180 512
    4 AffineBoundaryCached.sheets56 AffineBoundaryCached.shadows56
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt56
    (AffineBoundaryCached.checked56) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census57 : (AffineBoundaryCached.cert57).seeds.map Prod.fst = AffineSearchData.allowed57 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 57 is a boundary. -/
theorem boundary57 : TopFiberBoundary 0x6000000000004800580d8008003003000000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6000000000004800580d8008003003000000005000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete57 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert57).beta ∈
      (AffineBoundaryCached.cert57).seeds.map Prod.fst := by
    rw [census57]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert57) 180 512
    12 AffineBoundaryCached.sheets57 AffineBoundaryCached.shadows57
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt57
    (AffineBoundaryCached.checked57) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census58 : (AffineBoundaryCached.cert58).seeds.map Prod.fst = AffineSearchData.allowed58 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 58 is a boundary. -/
theorem boundary58 : TopFiberBoundary 0x6006000000000004806400c0008018003000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6006000000000004806400c0008018003000000005)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete58 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert58).beta ∈
      (AffineBoundaryCached.cert58).seeds.map Prod.fst := by
    rw [census58]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert58) 180 512
    12 AffineBoundaryCached.sheets58 AffineBoundaryCached.shadows58
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt58
    (AffineBoundaryCached.checked58) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census59 : (AffineBoundaryCached.cert59).seeds.map Prod.fst = AffineSearchData.allowed59 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 59 is a boundary. -/
theorem boundary59 : TopFiberBoundary 0x6014002000000000006c00c0018028003001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6014002000000000006c00c0018028003001000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete59 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert59).beta ∈
      (AffineBoundaryCached.cert59).seeds.map Prod.fst := by
    rw [census59]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert59) 180 512
    12 AffineBoundaryCached.sheets59 AffineBoundaryCached.shadows59
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt59
    (AffineBoundaryCached.checked59) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census60 : (AffineBoundaryCached.cert60).seeds.map Prod.fst = AffineSearchData.allowed60 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 60 is a boundary. -/
theorem boundary60 : TopFiberBoundary 0x6030006000000000006c00c0018000003003000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6030006000000000006c00c0018000003003000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete60 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert60).beta ∈
      (AffineBoundaryCached.cert60).seeds.map Prod.fst := by
    rw [census60]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert60) 180 512
    6 AffineBoundaryCached.sheets60 AffineBoundaryCached.shadows60
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt60
    (AffineBoundaryCached.checked60) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census61 : (AffineBoundaryCached.cert61).seeds.map Prod.fst = AffineSearchData.allowed61 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 61 is a boundary. -/
theorem boundary61 : TopFiberBoundary 0x6c01380380000000000000000030000006001c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6c01380380000000000000000030000006001c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete61 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert61).beta ∈
      (AffineBoundaryCached.cert61).seeds.map Prod.fst := by
    rw [census61]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert61) 180 512
    10 AffineBoundaryCached.sheets61 AffineBoundaryCached.shadows61
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt61
    (AffineBoundaryCached.checked61) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census62 : (AffineBoundaryCached.cert62).seeds.map Prod.fst = AffineSearchData.allowed62 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 62 is a boundary. -/
theorem boundary62 : TopFiberBoundary 0x7001000000000001f81c0000004007000800000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7001000000000001f81c0000004007000800000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete62 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert62).beta ∈
      (AffineBoundaryCached.cert62).seeds.map Prod.fst := by
    rw [census62]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert62) 180 512
    2 AffineBoundaryCached.sheets62 AffineBoundaryCached.shadows62
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt62
    (AffineBoundaryCached.checked62) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census63 : (AffineBoundaryCached.cert63).seeds.map Prod.fst = AffineSearchData.allowed63 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 63 is a boundary. -/
theorem boundary63 : TopFiberBoundary 0x7008001000000001f81c0000004004000800800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7008001000000001f81c0000004004000800800000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete63 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert63).beta ∈
      (AffineBoundaryCached.cert63).seeds.map Prod.fst := by
    rw [census63]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert63) 180 512
    2 AffineBoundaryCached.sheets63 AffineBoundaryCached.shadows63
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt63
    (AffineBoundaryCached.checked63) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census64 : (AffineBoundaryCached.cert64).seeds.map Prod.fst = AffineSearchData.allowed64 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 64 is a boundary. -/
theorem boundary64 : TopFiberBoundary 0x8008000000036009c08c0000020020004000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8008000000036009c08c0000020020004000018000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete64 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert64).beta ∈
      (AffineBoundaryCached.cert64).seeds.map Prod.fst := by
    rw [census64]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert64) 180 512
    4 AffineBoundaryCached.sheets64 AffineBoundaryCached.shadows64
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt64
    (AffineBoundaryCached.checked64) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census65 : (AffineBoundaryCached.cert65).seeds.map Prod.fst = AffineSearchData.allowed65 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 65 is a boundary. -/
theorem boundary65 : TopFiberBoundary 0xe00e00000000000000fc0000000038007000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe00e00000000000000fc0000000038007000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete65 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert65).beta ∈
      (AffineBoundaryCached.cert65).seeds.map Prod.fst := by
    rw [census65]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert65) 180 512
    6 AffineBoundaryCached.sheets65 AffineBoundaryCached.shadows65
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt65
    (AffineBoundaryCached.checked65) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census66 : (AffineBoundaryCached.cert66).seeds.map Prod.fst = AffineSearchData.allowed66 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 66 is a boundary. -/
theorem boundary66 : TopFiberBoundary 0xe01c00200000000000fc0000000008007001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xe01c00200000000000fc0000000008007001000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete66 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert66).beta ∈
      (AffineBoundaryCached.cert66).seeds.map Prod.fst := by
    rw [census66]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert66) 180 512
    2 AffineBoundaryCached.sheets66 AffineBoundaryCached.shadows66
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt66
    (AffineBoundaryCached.checked66) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census67 : (AffineBoundaryCached.cert67).seeds.map Prod.fst = AffineSearchData.allowed67 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 67 is a boundary. -/
theorem boundary67 : TopFiberBoundary 0xfc0038118004004000000800000000000800100100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0038118004004000000800000000000800100100)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete67 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert67).beta ∈
      (AffineBoundaryCached.cert67).seeds.map Prod.fst := by
    rw [census67]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert67) 180 512
    2 AffineBoundaryCached.sheets67 AffineBoundaryCached.shadows67
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt67
    (AffineBoundaryCached.checked67) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census68 : (AffineBoundaryCached.cert68).seeds.map Prod.fst = AffineSearchData.allowed68 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 68 is a boundary. -/
theorem boundary68 : TopFiberBoundary 0xfc0070030000000000000000000000c00e00180000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0070030000000000000000000000c00e00180000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete68 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert68).beta ∈
      (AffineBoundaryCached.cert68).seeds.map Prod.fst := by
    rw [census68]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert68) 180 512
    10 AffineBoundaryCached.sheets68 AffineBoundaryCached.shadows68
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt68
    (AffineBoundaryCached.checked68) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census69 : (AffineBoundaryCached.cert69).seeds.map Prod.fst = AffineSearchData.allowed69 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 69 is a boundary. -/
theorem boundary69 : TopFiberBoundary 0xfc01c0000000000900100000020000000e00000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0000000000900100000020000000e00000003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete69 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert69).beta ∈
      (AffineBoundaryCached.cert69).seeds.map Prod.fst := by
    rw [census69]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert69) 180 512
    12 AffineBoundaryCached.sheets69 AffineBoundaryCached.shadows69
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt69
    (AffineBoundaryCached.checked69) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census70 : (AffineBoundaryCached.cert70).seeds.map Prod.fst = AffineSearchData.allowed70 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 70 is a boundary. -/
theorem boundary70 : TopFiberBoundary 0xfc01c01200040040000008000000000008000c0100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c01200040040000008000000000008000c0100)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete70 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert70).beta ∈
      (AffineBoundaryCached.cert70).seeds.map Prod.fst := by
    rw [census70]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert70) 180 512
    12 AffineBoundaryCached.sheets70 AffineBoundaryCached.shadows70
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt70
    (AffineBoundaryCached.checked70) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census71 : (AffineBoundaryCached.cert71).seeds.map Prod.fst = AffineSearchData.allowed71 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 71 is a boundary. -/
theorem boundary71 : TopFiberBoundary 0x100000000000003f007240180e00008000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100000000000003f007240180e00008000000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete71 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert71).beta ∈
      (AffineBoundaryCached.cert71).seeds.map Prod.fst := by
    rw [census71]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert71) 180 512
    12 AffineBoundaryCached.sheets71 AffineBoundaryCached.shadows71
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt71
    (AffineBoundaryCached.checked71) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census72 : (AffineBoundaryCached.cert72).seeds.map Prod.fst = AffineSearchData.allowed72 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 72 is a boundary. -/
theorem boundary72 : TopFiberBoundary 0x10000000000001f8038240187000008000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000001f8038240187000008000000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete72 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert72).beta ∈
      (AffineBoundaryCached.cert72).seeds.map Prod.fst := by
    rw [census72]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert72) 180 512
    12 AffineBoundaryCached.sheets72 AffineBoundaryCached.shadows72
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt72
    (AffineBoundaryCached.checked72) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census73 : (AffineBoundaryCached.cert73).seeds.map Prod.fst = AffineSearchData.allowed73 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 73 is a boundary. -/
theorem boundary73 : TopFiberBoundary 0x1000000000000fc01c02401b8000008000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000000fc01c02401b8000008000000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete73 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert73).beta ∈
      (AffineBoundaryCached.cert73).seeds.map Prod.fst := by
    rw [census73]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert73) 180 512
    12 AffineBoundaryCached.sheets73 AffineBoundaryCached.shadows73
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt73
    (AffineBoundaryCached.checked73) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census74 : (AffineBoundaryCached.cert74).seeds.map Prod.fst = AffineSearchData.allowed74 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 74 is a boundary. -/
theorem boundary74 : TopFiberBoundary 0x100000000000208024028011001800800000002d003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100000000000208024028011001800800000002d003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete74 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert74).beta ∈
      (AffineBoundaryCached.cert74).seeds.map Prod.fst := by
    rw [census74]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert74) 180 512
    10 AffineBoundaryCached.sheets74 AffineBoundaryCached.shadows74
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt74
    (AffineBoundaryCached.checked74) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census75 : (AffineBoundaryCached.cert75).seeds.map Prod.fst = AffineSearchData.allowed75 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 75 is a boundary. -/
theorem boundary75 : TopFiberBoundary 0x1000000000002400bc0380100038008000000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000002400bc0380100038008000000028000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete75 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert75).beta ∈
      (AffineBoundaryCached.cert75).seeds.map Prod.fst := by
    rw [census75]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert75) 180 512
    14 AffineBoundaryCached.sheets75 AffineBoundaryCached.shadows75
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt75
    (AffineBoundaryCached.checked75) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census76 : (AffineBoundaryCached.cert76).seeds.map Prod.fst = AffineSearchData.allowed76 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 76 is a boundary. -/
theorem boundary76 : TopFiberBoundary 0x1000000000002407a00c401001c0008000000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000002407a00c401001c0008000000028000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete76 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert76).beta ∈
      (AffineBoundaryCached.cert76).seeds.map Prod.fst := by
    rw [census76]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert76) 180 512
    14 AffineBoundaryCached.sheets76 AffineBoundaryCached.shadows76
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt76
    (AffineBoundaryCached.checked76) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census77 : (AffineBoundaryCached.cert77).seeds.map Prod.fst = AffineSearchData.allowed77 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 77 is a boundary. -/
theorem boundary77 : TopFiberBoundary 0x10000000000048007c0380080038008000000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000048007c0380080038008000000018000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete77 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert77).beta ∈
      (AffineBoundaryCached.cert77).seeds.map Prod.fst := by
    rw [census77]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert77) 180 512
    10 AffineBoundaryCached.sheets77 AffineBoundaryCached.shadows77
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt77
    (AffineBoundaryCached.checked77) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census78 : (AffineBoundaryCached.cert78).seeds.map Prod.fst = AffineSearchData.allowed78 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 78 is a boundary. -/
theorem boundary78 : TopFiberBoundary 0x1000000000004807600c400801c0008000000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000004807600c400801c0008000000018000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete78 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert78).beta ∈
      (AffineBoundaryCached.cert78).seeds.map Prod.fst := by
    rw [census78]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert78) 180 512
    10 AffineBoundaryCached.sheets78 AffineBoundaryCached.shadows78
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt78
    (AffineBoundaryCached.checked78) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census79 : (AffineBoundaryCached.cert79).seeds.map Prod.fst = AffineSearchData.allowed79 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 79 is a boundary. -/
theorem boundary79 : TopFiberBoundary 0x1000000000006c003c0380000038008000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006c003c0380000038008000000030000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete79 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert79).beta ∈
      (AffineBoundaryCached.cert79).seeds.map Prod.fst := by
    rw [census79]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert79) 180 512
    6 AffineBoundaryCached.sheets79 AffineBoundaryCached.shadows79
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt79
    (AffineBoundaryCached.checked79) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census80 : (AffineBoundaryCached.cert80).seeds.map Prod.fst = AffineSearchData.allowed80 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 80 is a boundary. -/
theorem boundary80 : TopFiberBoundary 0x1000000000006c00ac0280000018008000000030003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006c00ac0280000018008000000030003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete80 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert80).beta ∈
      (AffineBoundaryCached.cert80).seeds.map Prod.fst := by
    rw [census80]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert80) 180 512
    10 AffineBoundaryCached.sheets80 AffineBoundaryCached.shadows80
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt80
    (AffineBoundaryCached.checked80) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census81 : (AffineBoundaryCached.cert81).seeds.map Prod.fst = AffineSearchData.allowed81 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 81 is a boundary. -/
theorem boundary81 : TopFiberBoundary 0x1000000000006c07200c400001c0008000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006c07200c400001c0008000000030000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete81 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert81).beta ∈
      (AffineBoundaryCached.cert81).seeds.map Prod.fst := by
    rw [census81]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert81) 180 512
    6 AffineBoundaryCached.sheets81 AffineBoundaryCached.shadows81
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt81
    (AffineBoundaryCached.checked81) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census82 : (AffineBoundaryCached.cert82).seeds.map Prod.fst = AffineSearchData.allowed82 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 82 is a boundary. -/
theorem boundary82 : TopFiberBoundary 0x1000000000007700f00240060000008000000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007700f00240060000008000000003000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete82 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert82).beta ∈
      (AffineBoundaryCached.cert82).seeds.map Prod.fst := by
    rw [census82]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert82) 180 512
    12 AffineBoundaryCached.sheets82 AffineBoundaryCached.shadows82
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt82
    (AffineBoundaryCached.checked82) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census83 : (AffineBoundaryCached.cert83).seeds.map Prod.fst = AffineSearchData.allowed83 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 83 is a boundary. -/
theorem boundary83 : TopFiberBoundary 0x1000000000007a80e80240050000008000000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007a80e80240050000008000000005000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete83 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert83).beta ∈
      (AffineBoundaryCached.cert83).seeds.map Prod.fst := by
    rw [census83]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert83) 180 512
    12 AffineBoundaryCached.sheets83 AffineBoundaryCached.shadows83
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt83
    (AffineBoundaryCached.checked83) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census84 : (AffineBoundaryCached.cert84).seeds.map Prod.fst = AffineSearchData.allowed84 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 84 is a boundary. -/
theorem boundary84 : TopFiberBoundary 0x1000000000007c40e40240048000008000000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007c40e40240048000008000000006000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete84 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert84).beta ∈
      (AffineBoundaryCached.cert84).seeds.map Prod.fst := by
    rw [census84]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert84) 180 512
    12 AffineBoundaryCached.sheets84 AffineBoundaryCached.shadows84
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt84
    (AffineBoundaryCached.checked84) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census85 : (AffineBoundaryCached.cert85).seeds.map Prod.fst = AffineSearchData.allowed85 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 85 is a boundary. -/
theorem boundary85 : TopFiberBoundary 0x1000000000007e00700340040020008000000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e00700340040020008000000000003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete85 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert85).beta ∈
      (AffineBoundaryCached.cert85).seeds.map Prod.fst := by
    rw [census85]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert85) 180 512
    12 AffineBoundaryCached.sheets85 AffineBoundaryCached.shadows85
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt85
    (AffineBoundaryCached.checked85) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census86 : (AffineBoundaryCached.cert86).seeds.map Prod.fst = AffineSearchData.allowed86 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 86 is a boundary. -/
theorem boundary86 : TopFiberBoundary 0x1000000000007e00a802c0040010008000000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e00a802c0040010008000000000005)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete86 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert86).beta ∈
      (AffineBoundaryCached.cert86).seeds.map Prod.fst := by
    rw [census86]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert86) 180 512
    12 AffineBoundaryCached.sheets86 AffineBoundaryCached.shadows86
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt86
    (AffineBoundaryCached.checked86) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census87 : (AffineBoundaryCached.cert87).seeds.map Prod.fst = AffineSearchData.allowed87 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 87 is a boundary. -/
theorem boundary87 : TopFiberBoundary 0x1000000000007e02a00640040080008000000000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e02a00640040080008000000000028)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete87 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert87).beta ∈
      (AffineBoundaryCached.cert87).seeds.map Prod.fst := by
    rw [census87]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert87) 180 512
    12 AffineBoundaryCached.sheets87 AffineBoundaryCached.shadows87
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt87
    (AffineBoundaryCached.checked87) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census88 : (AffineBoundaryCached.cert88).seeds.map Prod.fst = AffineSearchData.allowed88 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 88 is a boundary. -/
theorem boundary88 : TopFiberBoundary 0x1000000000007e04600a40040100008000000000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e04600a40040100008000000000018)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete88 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert88).beta ∈
      (AffineBoundaryCached.cert88).seeds.map Prod.fst := by
    rw [census88]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert88) 180 512
    12 AffineBoundaryCached.sheets88 AffineBoundaryCached.shadows88
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt88
    (AffineBoundaryCached.checked88) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census89 : (AffineBoundaryCached.cert89).seeds.map Prod.fst = AffineSearchData.allowed89 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 89 is a boundary. -/
theorem boundary89 : TopFiberBoundary 0x1000024020002c00c002400000000080c00c0010020 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000024020002c00c002400000000080c00c0010020)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete89 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert89).beta ∈
      (AffineBoundaryCached.cert89).seeds.map Prod.fst := by
    rw [census89]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert89) 180 512
    10 AffineBoundaryCached.sheets89 AffineBoundaryCached.shadows89
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt89
    (AffineBoundaryCached.checked89) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census90 : (AffineBoundaryCached.cert90).seeds.map Prod.fst = AffineSearchData.allowed90 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 90 is a boundary. -/
theorem boundary90 : TopFiberBoundary 0x1002400400007e00e00240040000020000002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1002400400007e00e00240040000020000002000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete90 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert90).beta ∈
      (AffineBoundaryCached.cert90).seeds.map Prod.fst := by
    rw [census90]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert90) 180 512
    12 AffineBoundaryCached.sheets90 AffineBoundaryCached.shadows90
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt90
    (AffineBoundaryCached.checked90) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census91 : (AffineBoundaryCached.cert91).seeds.map Prod.fst = AffineSearchData.allowed91 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 91 is a boundary. -/
theorem boundary91 : TopFiberBoundary 0x1004000000000001204140740080128020000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004000000000001204140740080128020000000030)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete91 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert91).beta ∈
      (AffineBoundaryCached.cert91).seeds.map Prod.fst := by
    rw [census91]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert91) 180 512
    10 AffineBoundaryCached.sheets91 AffineBoundaryCached.shadows91
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt91
    (AffineBoundaryCached.checked91) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census92 : (AffineBoundaryCached.cert92).seeds.map Prod.fst = AffineSearchData.allowed92 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 92 is a boundary. -/
theorem boundary92 : TopFiberBoundary 0x1004800800007e00e00240040000010000004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004800800007e00e00240040000010000004000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete92 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert92).beta ∈
      (AffineBoundaryCached.cert92).seeds.map Prod.fst := by
    rw [census92]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert92) 180 512
    12 AffineBoundaryCached.sheets92 AffineBoundaryCached.shadows92
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt92
    (AffineBoundaryCached.checked92) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census93 : (AffineBoundaryCached.cert93).seeds.map Prod.fst = AffineSearchData.allowed93 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 93 is a boundary. -/
theorem boundary93 : TopFiberBoundary 0x103f007000000000000240180000008000038000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x103f007000000000000240180000008000038000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete93 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert93).beta ∈
      (AffineBoundaryCached.cert93).seeds.map Prod.fst := by
    rw [census93]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert93) 180 512
    12 AffineBoundaryCached.sheets93 AffineBoundaryCached.shadows93
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt93
    (AffineBoundaryCached.checked93) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census94 : (AffineBoundaryCached.cert94).seeds.map Prod.fst = AffineSearchData.allowed94 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 94 is a boundary. -/
theorem boundary94 : TopFiberBoundary 0x1040240000000000fc01c000000e000001200000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1040240000000000fc01c000000e000001200000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete94 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert94).beta ∈
      (AffineBoundaryCached.cert94).seeds.map Prod.fst := by
    rw [census94]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert94) 180 512
    12 AffineBoundaryCached.sheets94 AffineBoundaryCached.shadows94
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt94
    (AffineBoundaryCached.checked94) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census95 : (AffineBoundaryCached.cert95).seeds.map Prod.fst = AffineSearchData.allowed95 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 95 is a boundary. -/
theorem boundary95 : TopFiberBoundary 0x11f80380000000000002401800000080001c0000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x11f80380000000000002401800000080001c0000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete95 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert95).beta ∈
      (AffineBoundaryCached.cert95).seeds.map Prod.fst := by
    rw [census95]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert95) 180 512
    12 AffineBoundaryCached.sheets95 AffineBoundaryCached.shadows95
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt95
    (AffineBoundaryCached.checked95) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census96 : (AffineBoundaryCached.cert96).seeds.map Prod.fst = AffineSearchData.allowed96 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 96 is a boundary. -/
theorem boundary96 : TopFiberBoundary 0x1200200000000002bc05c0000088000001000000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000002bc05c0000088000001000000028)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete96 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert96).beta ∈
      (AffineBoundaryCached.cert96).seeds.map Prod.fst := by
    rw [census96]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert96) 180 512
    12 AffineBoundaryCached.sheets96 AffineBoundaryCached.shadows96
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt96
    (AffineBoundaryCached.checked96) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census97 : (AffineBoundaryCached.cert97).seeds.map Prod.fst = AffineSearchData.allowed97 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 97 is a boundary. -/
theorem boundary97 : TopFiberBoundary 0x12002000000000047c09c0000108000001000000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000000047c09c0000108000001000000018)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete97 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert97).beta ∈
      (AffineBoundaryCached.cert97).seeds.map Prod.fst := by
    rw [census97]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert97) 180 512
    12 AffineBoundaryCached.sheets97 AffineBoundaryCached.shadows97
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt97
    (AffineBoundaryCached.checked97) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census98 : (AffineBoundaryCached.cert98).seeds.map Prod.fst = AffineSearchData.allowed98 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 98 is a boundary. -/
theorem boundary98 : TopFiberBoundary 0x1200200000000240f801c0008008000001000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000240f801c0008008000001000006000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete98 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert98).beta ∈
      (AffineBoundaryCached.cert98).seeds.map Prod.fst := by
    rw [census98]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert98) 180 512
    12 AffineBoundaryCached.sheets98 AffineBoundaryCached.shadows98
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt98
    (AffineBoundaryCached.checked98) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census99 : (AffineBoundaryCached.cert99).seeds.map Prod.fst = AffineSearchData.allowed99 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 99 is a boundary. -/
theorem boundary99 : TopFiberBoundary 0x1200200000000480f401c0010008000001000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000480f401c0010008000001000005000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete99 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert99).beta ∈
      (AffineBoundaryCached.cert99).seeds.map Prod.fst := by
    rw [census99]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert99) 180 512
    12 AffineBoundaryCached.sheets99 AffineBoundaryCached.shadows99
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt99
    (AffineBoundaryCached.checked99) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census100 : (AffineBoundaryCached.cert100).seeds.map Prod.fst = AffineSearchData.allowed100 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 100 is a boundary. -/
theorem boundary100 : TopFiberBoundary 0x1200200000000900ec01c0020008000001000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000900ec01c0020008000001000003000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete100 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert100).beta ∈
      (AffineBoundaryCached.cert100).seeds.map Prod.fst := by
    rw [census100]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert100) 180 512
    12 AffineBoundaryCached.sheets100 AffineBoundaryCached.shadows100
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt100
    (AffineBoundaryCached.checked100) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census101 : (AffineBoundaryCached.cert101).seeds.map Prod.fst = AffineSearchData.allowed101 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 101 is a boundary. -/
theorem boundary101 : TopFiberBoundary 0x1200200000001200dc01c0040008000001000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000001200dc01c0040008000001000030000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete101 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert101).beta ∈
      (AffineBoundaryCached.cert101).seeds.map Prod.fst := by
    rw [census101]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert101) 180 512
    12 AffineBoundaryCached.sheets101 AffineBoundaryCached.shadows101
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt101
    (AffineBoundaryCached.checked101) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census102 : (AffineBoundaryCached.cert102).seeds.map Prod.fst = AffineSearchData.allowed102 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 102 is a boundary. -/
theorem boundary102 : TopFiberBoundary 0x1200200000002400bc01c0080008000001000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000002400bc01c0080008000001000028000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete102 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert102).beta ∈
      (AffineBoundaryCached.cert102).seeds.map Prod.fst := by
    rw [census102]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert102) 180 512
    12 AffineBoundaryCached.sheets102 AffineBoundaryCached.shadows102
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt102
    (AffineBoundaryCached.checked102) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census103 : (AffineBoundaryCached.cert103).seeds.map Prod.fst = AffineSearchData.allowed103 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 103 is a boundary. -/
theorem boundary103 : TopFiberBoundary 0x12002000000048007c01c0100008000001000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000048007c01c0100008000001000018000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete103 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert103).beta ∈
      (AffineBoundaryCached.cert103).seeds.map Prod.fst := by
    rw [census103]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert103) 180 512
    12 AffineBoundaryCached.sheets103 AffineBoundaryCached.shadows103
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt103
    (AffineBoundaryCached.checked103) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty

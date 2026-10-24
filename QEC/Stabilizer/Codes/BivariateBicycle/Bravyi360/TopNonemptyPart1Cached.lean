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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart1
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census104 : (AffineBoundaryCached.cert104).seeds.map Prod.fst = AffineSearchData.allowed104 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 104 is a boundary. -/
theorem boundary104 : TopFiberBoundary 0x12003f80380000000000000000300000010001c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12003f80380000000000000000300000010001c0000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete104 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert104).beta ∈
      (AffineBoundaryCached.cert104).seeds.map Prod.fst := by
    rw [census104]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert104) 180 512
    12 AffineBoundaryCached.sheets104 AffineBoundaryCached.shadows104
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt104
    (AffineBoundaryCached.checked104) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census105 : (AffineBoundaryCached.cert105).seeds.map Prod.fst = AffineSearchData.allowed105 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 105 is a boundary. -/
theorem boundary105 : TopFiberBoundary 0x1201000200000000fc01c0000008030001001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1201000200000000fc01c0000008030001001000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete105 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert105).beta ∈
      (AffineBoundaryCached.cert105).seeds.map Prod.fst := by
    rw [census105]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert105) 180 512
    12 AffineBoundaryCached.sheets105 AffineBoundaryCached.shadows105
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt105
    (AffineBoundaryCached.checked105) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census106 : (AffineBoundaryCached.cert106).seeds.map Prod.fst = AffineSearchData.allowed106 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 106 is a boundary. -/
theorem boundary106 : TopFiberBoundary 0x1400400000000000fc07000c0010018002000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400400000000000fc07000c0010018002000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete106 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert106).beta ∈
      (AffineBoundaryCached.cert106).seeds.map Prod.fst := by
    rw [census106]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert106) 180 512
    6 AffineBoundaryCached.sheets106 AffineBoundaryCached.shadows106
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt106
    (AffineBoundaryCached.checked106) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census107 : (AffineBoundaryCached.cert107).seeds.map Prod.fst = AffineSearchData.allowed107 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 107 is a boundary. -/
theorem boundary107 : TopFiberBoundary 0x14032006000000000006c00c0028000002003000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x14032006000000000006c00c0028000002003000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete107 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert107).beta ∈
      (AffineBoundaryCached.cert107).seeds.map Prod.fst := by
    rw [census107]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert107) 180 512
    12 AffineBoundaryCached.sheets107 AffineBoundaryCached.shadows107
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt107
    (AffineBoundaryCached.checked107) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census108 : (AffineBoundaryCached.cert108).seeds.map Prod.fst = AffineSearchData.allowed108 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 108 is a boundary. -/
theorem boundary108 : TopFiberBoundary 0x16006000000000006c0440140000010003000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x16006000000000006c0440140000010003000000003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete108 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert108).beta ∈
      (AffineBoundaryCached.cert108).seeds.map Prod.fst := by
    rw [census108]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert108) 180 512
    12 AffineBoundaryCached.sheets108 AffineBoundaryCached.shadows108
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt108
    (AffineBoundaryCached.checked108) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census109 : (AffineBoundaryCached.cert109).seeds.map Prod.fst = AffineSearchData.allowed109 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 109 is a boundary. -/
theorem boundary109 : TopFiberBoundary 0x18008000000000006c0b80140000028004000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x18008000000000006c0b80140000028004000000003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete109 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert109).beta ∈
      (AffineBoundaryCached.cert109).seeds.map Prod.fst := by
    rw [census109]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert109) 180 512
    10 AffineBoundaryCached.sheets109 AffineBoundaryCached.shadows109
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt109
    (AffineBoundaryCached.checked109) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census110 : (AffineBoundaryCached.cert110).seeds.map Prod.fst = AffineSearchData.allowed110 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 110 is a boundary. -/
theorem boundary110 : TopFiberBoundary 0x1800800000000000fc0a80140020028004000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000000000fc0a80140020028004000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete110 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert110).beta ∈
      (AffineBoundaryCached.cert110).seeds.map Prod.fst := by
    rw [census110]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert110) 180 512
    8 AffineBoundaryCached.sheets110 AffineBoundaryCached.shadows110
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt110
    (AffineBoundaryCached.checked110) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census111 : (AffineBoundaryCached.cert111).seeds.map Prod.fst = AffineSearchData.allowed111 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 111 is a boundary. -/
theorem boundary111 : TopFiberBoundary 0x1800800000000001040900140050028004000000036 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000000001040900140050028004000000036)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete111 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert111).beta ∈
      (AffineBoundaryCached.cert111).seeds.map Prod.fst := by
    rw [census111]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert111) 180 512
    10 AffineBoundaryCached.sheets111 AffineBoundaryCached.shadows111
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt111
    (AffineBoundaryCached.checked111) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census112 : (AffineBoundaryCached.cert112).seeds.map Prod.fst = AffineSearchData.allowed112 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 112 is a boundary. -/
theorem boundary112 : TopFiberBoundary 0x1800800000001200040b00100010028004000030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000001200040b00100010028004000030006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete112 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert112).beta ∈
      (AffineBoundaryCached.cert112).seeds.map Prod.fst := by
    rw [census112]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert112) 180 512
    12 AffineBoundaryCached.sheets112 AffineBoundaryCached.shadows112
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt112
    (AffineBoundaryCached.checked112) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census113 : (AffineBoundaryCached.cert113).seeds.map Prod.fst = AffineSearchData.allowed113 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 113 is a boundary. -/
theorem boundary113 : TopFiberBoundary 0x1802c00400000000240b00140010000004002000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1802c00400000000240b00140010000004002000006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete113 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert113).beta ∈
      (AffineBoundaryCached.cert113).seeds.map Prod.fst := by
    rw [census113]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert113) 180 512
    10 AffineBoundaryCached.sheets113 AffineBoundaryCached.shadows113
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt113
    (AffineBoundaryCached.checked113) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census114 : (AffineBoundaryCached.cert114).seeds.map Prod.fst = AffineSearchData.allowed114 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 114 is a boundary. -/
theorem boundary114 : TopFiberBoundary 0x1804000800000000240b00140010030004004000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800000000240b00140010030004004000006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete114 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert114).beta ∈
      (AffineBoundaryCached.cert114).seeds.map Prod.fst := by
    rw [census114]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert114) 180 512
    12 AffineBoundaryCached.sheets114 AffineBoundaryCached.shadows114
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt114
    (AffineBoundaryCached.checked114) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census115 : (AffineBoundaryCached.cert115).seeds.map Prod.fst = AffineSearchData.allowed115 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 115 is a boundary. -/
theorem boundary115 : TopFiberBoundary 0x1805200a00000000000b40140018000004005000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1805200a00000000000b40140018000004005000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete115 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert115).beta ∈
      (AffineBoundaryCached.cert115).seeds.map Prod.fst := by
    rw [census115]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert115) 180 512
    12 AffineBoundaryCached.sheets115 AffineBoundaryCached.shadows115
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt115
    (AffineBoundaryCached.checked115) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census116 : (AffineBoundaryCached.cert116).seeds.map Prod.fst = AffineSearchData.allowed116 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 116 is a boundary. -/
theorem boundary116 : TopFiberBoundary 0x1a00a00000000000b408400c0000020005000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1a00a00000000000b408400c0000020005000000005)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete116 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert116).beta ∈
      (AffineBoundaryCached.cert116).seeds.map Prod.fst := by
    rw [census116]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert116) 180 512
    12 AffineBoundaryCached.sheets116 AffineBoundaryCached.shadows116
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt116
    (AffineBoundaryCached.checked116) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census117 : (AffineBoundaryCached.cert117).seeds.map Prod.fst = AffineSearchData.allowed117 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 117 is a boundary. -/
theorem boundary117 : TopFiberBoundary 0x1c02800400000000000fc0000030010006002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1c02800400000000000fc0000030010006002000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete117 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert117).beta ∈
      (AffineBoundaryCached.cert117).seeds.map Prod.fst := by
    rw [census117]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert117) 180 512
    8 AffineBoundaryCached.sheets117 AffineBoundaryCached.shadows117
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt117
    (AffineBoundaryCached.checked117) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census118 : (AffineBoundaryCached.cert118).seeds.map Prod.fst = AffineSearchData.allowed118 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 118 is a boundary. -/
theorem boundary118 : TopFiberBoundary 0x1c04400800000000000fc0000030020006004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1c04400800000000000fc0000030020006004000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete118 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert118).beta ∈
      (AffineBoundaryCached.cert118).seeds.map Prod.fst := by
    rw [census118]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert118) 180 512
    6 AffineBoundaryCached.sheets118 AffineBoundaryCached.shadows118
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt118
    (AffineBoundaryCached.checked118) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census119 : (AffineBoundaryCached.cert119).seeds.map Prod.fst = AffineSearchData.allowed119 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 119 is a boundary. -/
theorem boundary119 : TopFiberBoundary 0x3004800800002400080640040010000000004028005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3004800800002400080640040010000000004028005)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete119 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert119).beta ∈
      (AffineBoundaryCached.cert119).seeds.map Prod.fst := by
    rw [census119]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert119) 180 512
    10 AffineBoundaryCached.sheets119 AffineBoundaryCached.shadows119
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt119
    (AffineBoundaryCached.checked119) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census120 : (AffineBoundaryCached.cert120).seeds.map Prod.fst = AffineSearchData.allowed120 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 120 is a boundary. -/
theorem boundary120 : TopFiberBoundary 0x30048008000036006006c0000000000000004018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30048008000036006006c0000000000000004018000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete120 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert120).beta ∈
      (AffineBoundaryCached.cert120).seeds.map Prod.fst := by
    rw [census120]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert120) 180 512
    10 AffineBoundaryCached.sheets120 AffineBoundaryCached.shadows120
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt120
    (AffineBoundaryCached.checked120) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census121 : (AffineBoundaryCached.cert121).seeds.map Prod.fst = AffineSearchData.allowed121 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 121 is a boundary. -/
theorem boundary121 : TopFiberBoundary 0x3200200000004800580500040000010001000018006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3200200000004800580500040000010001000018006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete121 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert121).beta ∈
      (AffineBoundaryCached.cert121).seeds.map Prod.fst := by
    rw [census121]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert121) 180 512
    10 AffineBoundaryCached.sheets121 AffineBoundaryCached.shadows121
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt121
    (AffineBoundaryCached.checked121) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census122 : (AffineBoundaryCached.cert122).seeds.map Prod.fst = AffineSearchData.allowed122 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 122 is a boundary. -/
theorem boundary122 : TopFiberBoundary 0x3600600000000000fc01c0000020000003000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3600600000000000fc01c0000020000003000000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete122 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert122).beta ∈
      (AffineBoundaryCached.cert122).seeds.map Prod.fst := by
    rw [census122]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert122) 180 512
    18 AffineBoundaryCached.sheets122 AffineBoundaryCached.shadows122
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt122
    (AffineBoundaryCached.checked122) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census123 : (AffineBoundaryCached.cert123).seeds.map Prod.fst = AffineSearchData.allowed123 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 123 is a boundary. -/
theorem boundary123 : TopFiberBoundary 0x3804000800000000240f80000010020004004000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000000240f80000010020004004000006)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete123 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert123).beta ∈
      (AffineBoundaryCached.cert123).seeds.map Prod.fst := by
    rw [census123]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert123) 180 512
    4 AffineBoundaryCached.sheets123 AffineBoundaryCached.shadows123
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt123
    (AffineBoundaryCached.checked123) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census124 : (AffineBoundaryCached.cert124).seeds.map Prod.fst = AffineSearchData.allowed124 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 124 is a boundary. -/
theorem boundary124 : TopFiberBoundary 0x3804000800000000480f40000008020004004000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000000480f40000008020004004000005)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete124 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert124).beta ∈
      (AffineBoundaryCached.cert124).seeds.map Prod.fst := by
    rw [census124]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert124) 180 512
    6 AffineBoundaryCached.sheets124 AffineBoundaryCached.shadows124
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt124
    (AffineBoundaryCached.checked124) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census125 : (AffineBoundaryCached.cert125).seeds.map Prod.fst = AffineSearchData.allowed125 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 125 is a boundary. -/
theorem boundary125 : TopFiberBoundary 0x38040008000000006c0f00000000020004004000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38040008000000006c0f00000000020004004000003)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete125 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert125).beta ∈
      (AffineBoundaryCached.cert125).seeds.map Prod.fst := by
    rw [census125]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert125) 180 512
    4 AffineBoundaryCached.sheets125 AffineBoundaryCached.shadows125
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt125
    (AffineBoundaryCached.checked125) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census126 : (AffineBoundaryCached.cert126).seeds.map Prod.fst = AffineSearchData.allowed126 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 126 is a boundary. -/
theorem boundary126 : TopFiberBoundary 0x47c09c0120020000000000000018000004800000100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x47c09c0120020000000000000018000004800000100)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete126 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert126).beta ∈
      (AffineBoundaryCached.cert126).seeds.map Prod.fst := by
    rw [census126]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert126) 180 512
    12 AffineBoundaryCached.sheets126 AffineBoundaryCached.shadows126
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt126
    (AffineBoundaryCached.checked126) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census127 : (AffineBoundaryCached.cert127).seeds.map Prod.fst = AffineSearchData.allowed127 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 127 is a boundary. -/
theorem boundary127 : TopFiberBoundary 0x7008201200000000000fc0000000188000009000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7008201200000000000fc0000000188000009000000)/2 = 2 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete127 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert127).beta ∈
      (AffineBoundaryCached.cert127).seeds.map Prod.fst := by
    rw [census127]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert127) 180 512
    12 AffineBoundaryCached.sheets127 AffineBoundaryCached.shadows127
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt127
    (AffineBoundaryCached.checked127) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census128 : (AffineBoundaryCached.cert128).seeds.map Prod.fst = AffineSearchData.allowed128 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 128 is a boundary. -/
theorem boundary128 : TopFiberBoundary 0x6006000000000030c06c00c00c0018003000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x6006000000000030c06c00c00c0018003000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete128 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert128).beta ∈
      (AffineBoundaryCached.cert128).seeds.map Prod.fst := by
    rw [census128]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert128) 180 512
    2 AffineBoundaryCached.sheets128 AffineBoundaryCached.shadows128
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt128
    (AffineBoundaryCached.checked128) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census129 : (AffineBoundaryCached.cert129).seeds.map Prod.fst = AffineSearchData.allowed129 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 129 is a boundary. -/
theorem boundary129 : TopFiberBoundary 0x1000000000007e01e40d80040048008000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e01e40d80040048008000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete129 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert129).beta ∈
      (AffineBoundaryCached.cert129).seeds.map Prod.fst := by
    rw [census129]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert129) 180 512
    4 AffineBoundaryCached.sheets129 AffineBoundaryCached.shadows129
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt129
    (AffineBoundaryCached.checked129) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census130 : (AffineBoundaryCached.cert130).seeds.map Prod.fst = AffineSearchData.allowed130 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 130 is a boundary. -/
theorem boundary130 : TopFiberBoundary 0x11b82780000000000000000000360000013c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x11b82780000000000000000000360000013c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete130 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert130).beta ∈
      (AffineBoundaryCached.cert130).seeds.map Prod.fst := by
    rw [census130]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert130) 180 512
    6 AffineBoundaryCached.sheets130 AffineBoundaryCached.shadows130
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt130
    (AffineBoundaryCached.checked130) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census131 : (AffineBoundaryCached.cert131).seeds.map Prod.fst = AffineSearchData.allowed131 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 131 is a boundary. -/
theorem boundary131 : TopFiberBoundary 0x1800800000000005140b40140170028004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000000005140b40140170028004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete131 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert131).beta ∈
      (AffineBoundaryCached.cert131).seeds.map Prod.fst := by
    rw [census131]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert131) 180 512
    4 AffineBoundaryCached.sheets131 AffineBoundaryCached.shadows131
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt131
    (AffineBoundaryCached.checked131) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census132 : (AffineBoundaryCached.cert132).seeds.map Prod.fst = AffineSearchData.allowed132 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 132 is a boundary. -/
theorem boundary132 : TopFiberBoundary 0x1ce03e0000000000000000000030600001f00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1ce03e0000000000000000000030600001f00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete132 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert132).beta ∈
      (AffineBoundaryCached.cert132).seeds.map Prod.fst := by
    rw [census132]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert132) 180 512
    6 AffineBoundaryCached.sheets132 AffineBoundaryCached.shadows132
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt132
    (AffineBoundaryCached.checked132) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census133 : (AffineBoundaryCached.cert133).seeds.map Prod.fst = AffineSearchData.allowed133 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 133 is a boundary. -/
theorem boundary133 : TopFiberBoundary 0x1d503d0000000000000000000030a00001e80000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1d503d0000000000000000000030a00001e80000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete133 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert133).beta ∈
      (AffineBoundaryCached.cert133).seeds.map Prod.fst := by
    rw [census133]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert133) 180 512
    6 AffineBoundaryCached.sheets133 AffineBoundaryCached.shadows133
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt133
    (AffineBoundaryCached.checked133) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census134 : (AffineBoundaryCached.cert134).seeds.map Prod.fst = AffineSearchData.allowed134 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 134 is a boundary. -/
theorem boundary134 : TopFiberBoundary 0x1d883c8000000000000000000030c00001e40000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1d883c8000000000000000000030c00001e40000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete134 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert134).beta ∈
      (AffineBoundaryCached.cert134).seeds.map Prod.fst := by
    rw [census134]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert134) 180 512
    6 AffineBoundaryCached.sheets134 AffineBoundaryCached.shadows134
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt134
    (AffineBoundaryCached.checked134) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census135 : (AffineBoundaryCached.cert135).seeds.map Prod.fst = AffineSearchData.allowed135 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 135 is a boundary. -/
theorem boundary135 : TopFiberBoundary 0x7620f20000000000000000000003600007900000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7620f20000000000000000000003600007900000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete135 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert135).beta ∈
      (AffineBoundaryCached.cert135).seeds.map Prod.fst := by
    rw [census135]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert135) 180 512
    6 AffineBoundaryCached.sheets135 AffineBoundaryCached.shadows135
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt135
    (AffineBoundaryCached.checked135) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census136 : (AffineBoundaryCached.cert136).seeds.map Prod.fst = AffineSearchData.allowed136 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 136 is a boundary. -/
theorem boundary136 : TopFiberBoundary 0x8601600000000002080b4014010801000b000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8601600000000002080b4014010801000b000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete136 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert136).beta ∈
      (AffineBoundaryCached.cert136).seeds.map Prod.fst := by
    rw [census136]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert136) 180 512
    4 AffineBoundaryCached.sheets136 AffineBoundaryCached.shadows136
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt136
    (AffineBoundaryCached.checked136) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census137 : (AffineBoundaryCached.cert137).seeds.map Prod.fst = AffineSearchData.allowed137 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 137 is a boundary. -/
theorem boundary137 : TopFiberBoundary 0xa0010000000000030c06c00c0158018008000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xa0010000000000030c06c00c0158018008000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete137 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert137).beta ∈
      (AffineBoundaryCached.cert137).seeds.map Prod.fst := by
    rw [census137]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert137) 180 512
    4 AffineBoundaryCached.sheets137 AffineBoundaryCached.shadows137
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt137
    (AffineBoundaryCached.checked137) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census138 : (AffineBoundaryCached.cert138).seeds.map Prod.fst = AffineSearchData.allowed138 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 138 is a boundary. -/
theorem boundary138 : TopFiberBoundary 0x180030000000000030c06c00c0018018018000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x180030000000000030c06c00c0018018018000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete138 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert138).beta ∈
      (AffineBoundaryCached.cert138).seeds.map Prod.fst := by
    rw [census138]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert138) 180 512
    2 AffineBoundaryCached.sheets138 AffineBoundaryCached.shadows138
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt138
    (AffineBoundaryCached.checked138) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census139 : (AffineBoundaryCached.cert139).seeds.map Prod.fst = AffineSearchData.allowed139 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 139 is a boundary. -/
theorem boundary139 : TopFiberBoundary 0x18203200000000002080b40140060010019000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x18203200000000002080b40140060010019000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete139 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert139).beta ∈
      (AffineBoundaryCached.cert139).seeds.map Prod.fst := by
    rw [census139]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert139) 180 512
    4 AffineBoundaryCached.sheets139 AffineBoundaryCached.shadows139
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt139
    (AffineBoundaryCached.checked139) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census140 : (AffineBoundaryCached.cert140).seeds.map Prod.fst = AffineSearchData.allowed140 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 140 is a boundary. -/
theorem boundary140 : TopFiberBoundary 0x40001248000000000000000000db6c00049240000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x40001248000000000000000000db6c00049240000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete140 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert140).beta ∈
      (AffineBoundaryCached.cert140).seeds.map Prod.fst := by
    rw [census140]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert140) 180 512
    10 AffineBoundaryCached.sheets140 AffineBoundaryCached.shadows140
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt140
    (AffineBoundaryCached.checked140) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census141 : (AffineBoundaryCached.cert141).seeds.map Prod.fst = AffineSearchData.allowed141 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 141 is a boundary. -/
theorem boundary141 : TopFiberBoundary 0x402400000000006c028018002e008001200000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x402400000000006c028018002e008001200000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete141 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert141).beta ∈
      (AffineBoundaryCached.cert141).seeds.map Prod.fst := by
    rw [census141]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert141) 180 512
    8 AffineBoundaryCached.sheets141 AffineBoundaryCached.shadows141
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt141
    (AffineBoundaryCached.checked141) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census142 : (AffineBoundaryCached.cert142).seeds.map Prod.fst = AffineSearchData.allowed142 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 142 is a boundary. -/
theorem boundary142 : TopFiberBoundary 0x40240000000000fc038018000e008001200000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x40240000000000fc038018000e008001200000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete142 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert142).beta ∈
      (AffineBoundaryCached.cert142).seeds.map Prod.fst := by
    rw [census142]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert142) 180 512
    2 AffineBoundaryCached.sheets142 AffineBoundaryCached.shadows142
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt142
    (AffineBoundaryCached.checked142) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census143 : (AffineBoundaryCached.cert143).seeds.map Prod.fst = AffineSearchData.allowed143 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 143 is a boundary. -/
theorem boundary143 : TopFiberBoundary 0x40b00140000000048070030007004000200a00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x40b00140000000048070030007004000200a00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete143 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert143).beta ∈
      (AffineBoundaryCached.cert143).seeds.map Prod.fst := by
    rw [census143]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert143) 180 512
    8 AffineBoundaryCached.sheets143 AffineBoundaryCached.shadows143
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt143
    (AffineBoundaryCached.checked143) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census144 : (AffineBoundaryCached.cert144).seeds.map Prod.fst = AffineSearchData.allowed144 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 144 is a boundary. -/
theorem boundary144 : TopFiberBoundary 0x411f1038000000000000000000d800000481c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x411f1038000000000000000000d800000481c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete144 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert144).beta ∈
      (AffineBoundaryCached.cert144).seeds.map Prod.fst := by
    rw [census144]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert144) 180 512
    6 AffineBoundaryCached.sheets144 AffineBoundaryCached.shadows144
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt144
    (AffineBoundaryCached.checked144) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census145 : (AffineBoundaryCached.cert145).seeds.map Prod.fst = AffineSearchData.allowed145 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 145 is a boundary. -/
theorem boundary145 : TopFiberBoundary 0x45840a00000000000240180036020001205000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x45840a00000000000240180036020001205000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete145 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert145).beta ∈
      (AffineBoundaryCached.cert145).seeds.map Prod.fst := by
    rw [census145]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert145) 180 512
    8 AffineBoundaryCached.sheets145 AffineBoundaryCached.shadows145
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt145
    (AffineBoundaryCached.checked145) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census146 : (AffineBoundaryCached.cert146).seeds.map Prod.fst = AffineSearchData.allowed146 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 146 is a boundary. -/
theorem boundary146 : TopFiberBoundary 0x483b0078000000000000000000c060000403c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x483b0078000000000000000000c060000403c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete146 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert146).beta ∈
      (AffineBoundaryCached.cert146).seeds.map Prod.fst := by
    rw [census146]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert146) 180 512
    6 AffineBoundaryCached.sheets146 AffineBoundaryCached.shadows146
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt146
    (AffineBoundaryCached.checked146) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census147 : (AffineBoundaryCached.cert147).seeds.map Prod.fst = AffineSearchData.allowed147 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 147 is a boundary. -/
theorem boundary147 : TopFiberBoundary 0x485700b8000000000000000000c050000405c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x485700b8000000000000000000c050000405c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete147 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert147).beta ∈
      (AffineBoundaryCached.cert147).seeds.map Prod.fst := by
    rw [census147]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert147) 180 512
    6 AffineBoundaryCached.sheets147 AffineBoundaryCached.shadows147
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt147
    (AffineBoundaryCached.checked147) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census148 : (AffineBoundaryCached.cert148).seeds.map Prod.fst = AffineSearchData.allowed148 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 148 is a boundary. -/
theorem boundary148 : TopFiberBoundary 0x488f0138000000000000000000c030000409c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x488f0138000000000000000000c030000409c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete148 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert148).beta ∈
      (AffineBoundaryCached.cert148).seeds.map Prod.fst := by
    rw [census148]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert148) 180 512
    6 AffineBoundaryCached.sheets148 AffineBoundaryCached.shadows148
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt148
    (AffineBoundaryCached.checked148) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census149 : (AffineBoundaryCached.cert149).seeds.map Prod.fst = AffineSearchData.allowed149 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 149 is a boundary. -/
theorem boundary149 : TopFiberBoundary 0x48f801c8000000000000000000c00c00040e40000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x48f801c8000000000000000000c00c00040e40000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete149 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert149).beta ∈
      (AffineBoundaryCached.cert149).seeds.map Prod.fst := by
    rw [census149]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert149) 180 512
    6 AffineBoundaryCached.sheets149 AffineBoundaryCached.shadows149
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt149
    (AffineBoundaryCached.checked149) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census150 : (AffineBoundaryCached.cert150).seeds.map Prod.fst = AffineSearchData.allowed150 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 150 is a boundary. -/
theorem boundary150 : TopFiberBoundary 0x5805000800000008202d0050022008000c0040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x5805000800000008202d0050022008000c0040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete150 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert150).beta ∈
      (AffineBoundaryCached.cert150).seeds.map Prod.fst := by
    rw [census150]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert150) 180 512
    4 AffineBoundaryCached.sheets150 AffineBoundaryCached.shadows150
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt150
    (AffineBoundaryCached.checked150) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census151 : (AffineBoundaryCached.cert151).seeds.map Prod.fst = AffineSearchData.allowed151 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 151 is a boundary. -/
theorem boundary151 : TopFiberBoundary 0x77047008000000000000000000c00c00078040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x77047008000000000000000000c00c00078040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete151 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert151).beta ∈
      (AffineBoundaryCached.cert151).seeds.map Prod.fst := by
    rw [census151]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert151) 180 512
    6 AffineBoundaryCached.sheets151 AffineBoundaryCached.shadows151
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt151
    (AffineBoundaryCached.checked151) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census152 : (AffineBoundaryCached.cert152).seeds.map Prod.fst = AffineSearchData.allowed152 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 152 is a boundary. -/
theorem boundary152 : TopFiberBoundary 0xc00c0000000000298098018008003000600000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xc00c0000000000298098018008003000600000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete152 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert152).beta ∈
      (AffineBoundaryCached.cert152).seeds.map Prod.fst := by
    rw [census152]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert152) 180 512
    2 AffineBoundaryCached.sheets152 AffineBoundaryCached.shadows152
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt152
    (AffineBoundaryCached.checked152) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census153 : (AffineBoundaryCached.cert153).seeds.map Prod.fst = AffineSearchData.allowed153 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 153 is a boundary. -/
theorem boundary153 : TopFiberBoundary 0xc00c0000000000458058018010003000600000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xc00c0000000000458058018010003000600000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete153 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert153).beta ∈
      (AffineBoundaryCached.cert153).seeds.map Prod.fst := by
    rw [census153]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert153) 180 512
    2 AffineBoundaryCached.sheets153 AffineBoundaryCached.shadows153
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt153
    (AffineBoundaryCached.checked153) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census154 : (AffineBoundaryCached.cert154).seeds.map Prod.fst = AffineSearchData.allowed154 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 154 is a boundary. -/
theorem boundary154 : TopFiberBoundary 0xc04400800000000d80d8018000006000600400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xc04400800000000d80d8018000006000600400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete154 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert154).beta ∈
      (AffineBoundaryCached.cert154).seeds.map Prod.fst := by
    rw [census154]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert154) 180 512
    2 AffineBoundaryCached.sheets154 AffineBoundaryCached.shadows154
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt154
    (AffineBoundaryCached.checked154) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census155 : (AffineBoundaryCached.cert155).seeds.map Prod.fst = AffineSearchData.allowed155 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 155 is a boundary. -/
theorem boundary155 : TopFiberBoundary 0xc09c01000000000d80d8018000000000600800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xc09c01000000000d80d8018000000000600800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete155 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert155).beta ∈
      (AffineBoundaryCached.cert155).seeds.map Prod.fst := by
    rw [census155]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert155) 180 512
    2 AffineBoundaryCached.sheets155 AffineBoundaryCached.shadows155
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt155
    (AffineBoundaryCached.checked155) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census156 : (AffineBoundaryCached.cert156).seeds.map Prod.fst = AffineSearchData.allowed156 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 156 is a boundary. -/
theorem boundary156 : TopFiberBoundary 0x140140000000900068168008000005000a00003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x140140000000900068168008000005000a00003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete156 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert156).beta ∈
      (AffineBoundaryCached.cert156).seeds.map Prod.fst := by
    rw [census156]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert156) 180 512
    2 AffineBoundaryCached.sheets156 AffineBoundaryCached.shadows156
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt156
    (AffineBoundaryCached.checked156) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census157 : (AffineBoundaryCached.cert157).seeds.map Prod.fst = AffineSearchData.allowed157 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 157 is a boundary. -/
theorem boundary157 : TopFiberBoundary 0x16800c020000800800000100000a000c0180038020 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x16800c020000800800000100000a000c0180038020)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete157 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert157).beta ∈
      (AffineBoundaryCached.cert157).seeds.map Prod.fst := by
    rw [census157]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert157) 180 512
    8 AffineBoundaryCached.sheets157 AffineBoundaryCached.shadows157
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt157
    (AffineBoundaryCached.checked157) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census158 : (AffineBoundaryCached.cert158).seeds.map Prod.fst = AffineSearchData.allowed158 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 158 is a boundary. -/
theorem boundary158 : TopFiberBoundary 0x1dc0740080000000000000000000c0c001e0040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1dc0740080000000000000000000c0c001e0040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete158 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert158).beta ∈
      (AffineBoundaryCached.cert158).seeds.map Prod.fst := by
    rw [census158]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert158) 180 512
    6 AffineBoundaryCached.sheets158 AffineBoundaryCached.shadows158
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt158
    (AffineBoundaryCached.checked158) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census159 : (AffineBoundaryCached.cert159).seeds.map Prod.fst = AffineSearchData.allowed159 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 159 is a boundary. -/
theorem boundary159 : TopFiberBoundary 0x1dc0ac0100000000000000000000c0a001e0080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1dc0ac0100000000000000000000c0a001e0080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete159 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert159).beta ∈
      (AffineBoundaryCached.cert159).seeds.map Prod.fst := by
    rw [census159]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert159) 180 512
    6 AffineBoundaryCached.sheets159 AffineBoundaryCached.shadows159
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt159
    (AffineBoundaryCached.checked159) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census160 : (AffineBoundaryCached.cert160).seeds.map Prod.fst = AffineSearchData.allowed160 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 160 is a boundary. -/
theorem boundary160 : TopFiberBoundary 0x1dc11c0200000000000000000000c06001e0100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1dc11c0200000000000000000000c06001e0100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete160 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert160).beta ∈
      (AffineBoundaryCached.cert160).seeds.map Prod.fst := by
    rw [census160]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert160) 180 512
    6 AffineBoundaryCached.sheets160 AffineBoundaryCached.shadows160
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt160
    (AffineBoundaryCached.checked160) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census161 : (AffineBoundaryCached.cert161).seeds.map Prod.fst = AffineSearchData.allowed161 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 161 is a boundary. -/
theorem boundary161 : TopFiberBoundary 0x1f801c0200008008000001000000000c0100038020 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f801c0200008008000001000000000c0100038020)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete161 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert161).beta ∈
      (AffineBoundaryCached.cert161).seeds.map Prod.fst := by
    rw [census161]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert161) 180 512
    2 AffineBoundaryCached.sheets161 AffineBoundaryCached.shadows161
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt161
    (AffineBoundaryCached.checked161) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census162 : (AffineBoundaryCached.cert162).seeds.map Prod.fst = AffineSearchData.allowed162 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 162 is a boundary. -/
theorem boundary162 : TopFiberBoundary 0x1f8230048000000000000000000006c001c0240000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1f8230048000000000000000000006c001c0240000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete162 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert162).beta ∈
      (AffineBoundaryCached.cert162).seeds.map Prod.fst := by
    rw [census162]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert162) 180 512
    6 AffineBoundaryCached.sheets162 AffineBoundaryCached.shadows162
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt162
    (AffineBoundaryCached.checked162) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census163 : (AffineBoundaryCached.cert163).seeds.map Prod.fst = AffineSearchData.allowed163 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 163 is a boundary. -/
theorem boundary163 : TopFiberBoundary 0x2000000000001f8070070037001001000000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000001f8070070037001001000000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete163 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert163).beta ∈
      (AffineBoundaryCached.cert163).seeds.map Prod.fst := by
    rw [census163]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert163) 180 512
    6 AffineBoundaryCached.sheets163 AffineBoundaryCached.shadows163
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt163
    (AffineBoundaryCached.checked163) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census164 : (AffineBoundaryCached.cert164).seeds.map Prod.fst = AffineSearchData.allowed164 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 164 is a boundary. -/
theorem boundary164 : TopFiberBoundary 0x2000000000004580d0070023001001000000005600 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000004580d0070023001001000000005600)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete164 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert164).beta ∈
      (AffineBoundaryCached.cert164).seeds.map Prod.fst := by
    rw [census164]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert164) 180 512
    10 AffineBoundaryCached.sheets164 AffineBoundaryCached.shadows164
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt164
    (AffineBoundaryCached.checked164) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census165 : (AffineBoundaryCached.cert165).seeds.map Prod.fst = AffineSearchData.allowed165 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 165 is a boundary. -/
theorem boundary165 : TopFiberBoundary 0x200000000000480f081b0020039001000000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000480f081b0020039001000000005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete165 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert165).beta ∈
      (AffineBoundaryCached.cert165).seeds.map Prod.fst := by
    rw [census165]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert165) 180 512
    2 AffineBoundaryCached.sheets165 AffineBoundaryCached.shadows165
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt165
    (AffineBoundaryCached.checked165) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census166 : (AffineBoundaryCached.cert166).seeds.map Prod.fst = AffineSearchData.allowed166 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 166 is a boundary. -/
theorem boundary166 : TopFiberBoundary 0x20000000000061809007002b001001000000003600 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x20000000000061809007002b001001000000003600)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete166 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert166).beta ∈
      (AffineBoundaryCached.cert166).seeds.map Prod.fst := by
    rw [census166]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert166) 180 512
    4 AffineBoundaryCached.sheets166 AffineBoundaryCached.shadows166
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt166
    (AffineBoundaryCached.checked166) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census167 : (AffineBoundaryCached.cert167).seeds.map Prod.fst = AffineSearchData.allowed167 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 167 is a boundary. -/
theorem boundary167 : TopFiberBoundary 0x20000000000065009807002a001001000000003a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x20000000000065009807002a001001000000003a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete167 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert167).beta ∈
      (AffineBoundaryCached.cert167).seeds.map Prod.fst := by
    rw [census167]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert167) 180 512
    8 AffineBoundaryCached.sheets167 AffineBoundaryCached.shadows167
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt167
    (AffineBoundaryCached.checked167) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census168 : (AffineBoundaryCached.cert168).seeds.map Prod.fst = AffineSearchData.allowed168 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 168 is a boundary. -/
theorem boundary168 : TopFiberBoundary 0x2000000000006c04080f0028011001000000003005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000006c04080f0028011001000000003005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete168 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert168).beta ∈
      (AffineBoundaryCached.cert168).seeds.map Prod.fst := by
    rw [census168]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert168) 180 512
    8 AffineBoundaryCached.sheets168 AffineBoundaryCached.shadows168
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt168
    (AffineBoundaryCached.checked168) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census169 : (AffineBoundaryCached.cert169).seeds.map Prod.fst = AffineSearchData.allowed169 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 169 is a boundary. -/
theorem boundary169 : TopFiberBoundary 0x200000000000900e881b0010039001000000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000900e881b0010039001000000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete169 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert169).beta ∈
      (AffineBoundaryCached.cert169).seeds.map Prod.fst := by
    rw [census169]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert169) 180 512
    4 AffineBoundaryCached.sheets169 AffineBoundaryCached.shadows169
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt169
    (AffineBoundaryCached.checked169) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census170 : (AffineBoundaryCached.cert170).seeds.map Prod.fst = AffineSearchData.allowed170 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 170 is a boundary. -/
theorem boundary170 : TopFiberBoundary 0x200000000000d807080b0000019001000000006003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000d807080b0000019001000000006003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete170 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert170).beta ∈
      (AffineBoundaryCached.cert170).seeds.map Prod.fst := by
    rw [census170]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert170) 180 512
    4 AffineBoundaryCached.sheets170 AffineBoundaryCached.shadows170
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt170
    (AffineBoundaryCached.checked170) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census171 : (AffineBoundaryCached.cert171).seeds.map Prod.fst = AffineSearchData.allowed171 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 171 is a boundary. -/
theorem boundary171 : TopFiberBoundary 0x200000000000d80e081b0000039001000000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000d80e081b0000039001000000006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete171 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert171).beta ∈
      (AffineBoundaryCached.cert171).seeds.map Prod.fst := by
    rw [census171]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert171) 180 512
    2 AffineBoundaryCached.sheets171 AffineBoundaryCached.shadows171
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt171
    (AffineBoundaryCached.checked171) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census172 : (AffineBoundaryCached.cert172).seeds.map Prod.fst = AffineSearchData.allowed172 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 172 is a boundary. -/
theorem boundary172 : TopFiberBoundary 0x200000000000ea81a007000d001001000000000a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000ea81a007000d001001000000000a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete172 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert172).beta ∈
      (AffineBoundaryCached.cert172).seeds.map Prod.fst := by
    rw [census172]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert172) 180 512
    2 AffineBoundaryCached.sheets172 AffineBoundaryCached.shadows172
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt172
    (AffineBoundaryCached.checked172) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census173 : (AffineBoundaryCached.cert173).seeds.map Prod.fst = AffineSearchData.allowed173 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 173 is a boundary. -/
theorem boundary173 : TopFiberBoundary 0x200000000000ee01a807000c001001000000000600 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000ee01a807000c001001000000000600)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete173 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert173).beta ∈
      (AffineBoundaryCached.cert173).seeds.map Prod.fst := by
    rw [census173]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert173) 180 512
    2 AffineBoundaryCached.sheets173 AffineBoundaryCached.shadows173
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt173
    (AffineBoundaryCached.checked173) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census174 : (AffineBoundaryCached.cert174).seeds.map Prod.fst = AffineSearchData.allowed174 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 174 is a boundary. -/
theorem boundary174 : TopFiberBoundary 0x200000000000f5019807000a001001000000000a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000f5019807000a001001000000000a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete174 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert174).beta ∈
      (AffineBoundaryCached.cert174).seeds.map Prod.fst := by
    rw [census174]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert174) 180 512
    2 AffineBoundaryCached.sheets174 AffineBoundaryCached.shadows174
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt174
    (AffineBoundaryCached.checked174) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census175 : (AffineBoundaryCached.cert175).seeds.map Prod.fst = AffineSearchData.allowed175 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 175 is a boundary. -/
theorem boundary175 : TopFiberBoundary 0x200000000000fc05080f0008011001000000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000fc05080f0008011001000000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete175 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert175).beta ∈
      (AffineBoundaryCached.cert175).seeds.map Prod.fst := by
    rw [census175]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert175) 180 512
    2 AffineBoundaryCached.sheets175 AffineBoundaryCached.shadows175
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt175
    (AffineBoundaryCached.checked175) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census176 : (AffineBoundaryCached.cert176).seeds.map Prod.fst = AffineSearchData.allowed176 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 176 is a boundary. -/
theorem boundary176 : TopFiberBoundary 0x200000000000fc0888170008021001000000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200000000000fc0888170008021001000000000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete176 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert176).beta ∈
      (AffineBoundaryCached.cert176).seeds.map Prod.fst := by
    rw [census176]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert176) 180 512
    2 AffineBoundaryCached.sheets176 AffineBoundaryCached.shadows176
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt176
    (AffineBoundaryCached.checked176) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census177 : (AffineBoundaryCached.cert177).seeds.map Prod.fst = AffineSearchData.allowed177 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 177 is a boundary. -/
theorem boundary177 : TopFiberBoundary 0x2000400400000006c028018002800e001000200003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000400400000006c028018002800e001000200003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete177 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert177).beta ∈
      (AffineBoundaryCached.cert177).seeds.map Prod.fst := by
    rw [census177]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert177) 180 512
    8 AffineBoundaryCached.sheets177 AffineBoundaryCached.shadows177
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt177
    (AffineBoundaryCached.checked177) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census178 : (AffineBoundaryCached.cert178).seeds.map Prod.fst = AffineSearchData.allowed178 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 178 is a boundary. -/
theorem boundary178 : TopFiberBoundary 0x200040040000000fc038018000800e001000200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200040040000000fc038018000800e001000200000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete178 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert178).beta ∈
      (AffineBoundaryCached.cert178).seeds.map Prod.fst := by
    rw [census178]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert178) 180 512
    2 AffineBoundaryCached.sheets178 AffineBoundaryCached.shadows178
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt178
    (AffineBoundaryCached.checked178) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census179 : (AffineBoundaryCached.cert179).seeds.map Prod.fst = AffineSearchData.allowed179 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 179 is a boundary. -/
theorem boundary179 : TopFiberBoundary 0x2002000000000022c06801800a800800100000002b := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000022c06801800a800800100000002b)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete179 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert179).beta ∈
      (AffineBoundaryCached.cert179).seeds.map Prod.fst := by
    rw [census179]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert179) 180 512
    8 AffineBoundaryCached.sheets179 AffineBoundaryCached.shadows179
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt179
    (AffineBoundaryCached.checked179) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census180 : (AffineBoundaryCached.cert180).seeds.map Prod.fst = AffineSearchData.allowed180 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 180 is a boundary. -/
theorem boundary180 : TopFiberBoundary 0x200200000000002bc0780180088008001000000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000002bc0780180088008001000000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete180 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert180).beta ∈
      (AffineBoundaryCached.cert180).seeds.map Prod.fst := by
    rw [census180]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert180) 180 512
    2 AffineBoundaryCached.sheets180 AffineBoundaryCached.shadows180
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt180
    (AffineBoundaryCached.checked180) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census181 : (AffineBoundaryCached.cert181).seeds.map Prod.fst = AffineSearchData.allowed181 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 181 is a boundary. -/
theorem boundary181 : TopFiberBoundary 0x2002000000000030c04801800e800800100000001b := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000030c04801800e800800100000001b)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete181 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert181).beta ∈
      (AffineBoundaryCached.cert181).seeds.map Prod.fst := by
    rw [census181]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert181) 180 512
    4 AffineBoundaryCached.sheets181 AffineBoundaryCached.shadows181
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt181
    (AffineBoundaryCached.checked181) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census182 : (AffineBoundaryCached.cert182).seeds.map Prod.fst = AffineSearchData.allowed182 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 182 is a boundary. -/
theorem boundary182 : TopFiberBoundary 0x2002000000000032804c01800e000800100000001d := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000032804c01800e000800100000001d)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete182 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert182).beta ∈
      (AffineBoundaryCached.cert182).seeds.map Prod.fst := by
    rw [census182]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert182) 180 512
    10 AffineBoundaryCached.sheets182 AffineBoundaryCached.shadows182
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt182
    (AffineBoundaryCached.checked182) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census183 : (AffineBoundaryCached.cert183).seeds.map Prod.fst = AffineSearchData.allowed183 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 183 is a boundary. -/
theorem boundary183 : TopFiberBoundary 0x2002000000000047c0b80180108008001000000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000047c0b80180108008001000000018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete183 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert183).beta ∈
      (AffineBoundaryCached.cert183).seeds.map Prod.fst := by
    rw [census183]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert183) 180 512
    2 AffineBoundaryCached.sheets183 AffineBoundaryCached.shadows183
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt183
    (AffineBoundaryCached.checked183) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census184 : (AffineBoundaryCached.cert184).seeds.map Prod.fst = AffineSearchData.allowed184 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 184 is a boundary. -/
theorem boundary184 : TopFiberBoundary 0x2002000000000055c0980180148008001000000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2002000000000055c0980180148008001000000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete184 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert184).beta ∈
      (AffineBoundaryCached.cert184).seeds.map Prod.fst := by
    rw [census184]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert184) 180 512
    2 AffineBoundaryCached.sheets184 AffineBoundaryCached.shadows184
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt184
    (AffineBoundaryCached.checked184) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census185 : (AffineBoundaryCached.cert185).seeds.map Prod.fst = AffineSearchData.allowed185 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 185 is a boundary. -/
theorem boundary185 : TopFiberBoundary 0x200200000000007e00c401801f0008001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000007e00c401801f0008001000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete185 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert185).beta ∈
      (AffineBoundaryCached.cert185).seeds.map Prod.fst := by
    rw [census185]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert185) 180 512
    6 AffineBoundaryCached.sheets185 AffineBoundaryCached.shadows185
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt185
    (AffineBoundaryCached.checked185) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census186 : (AffineBoundaryCached.cert186).seeds.map Prod.fst = AffineSearchData.allowed186 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 186 is a boundary. -/
theorem boundary186 : TopFiberBoundary 0x200200000000240680280188028008001000006003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000240680280188028008001000006003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete186 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert186).beta ∈
      (AffineBoundaryCached.cert186).seeds.map Prod.fst := by
    rw [census186]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert186) 180 512
    8 AffineBoundaryCached.sheets186 AffineBoundaryCached.shadows186
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt186
    (AffineBoundaryCached.checked186) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census187 : (AffineBoundaryCached.cert187).seeds.map Prod.fst = AffineSearchData.allowed187 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 187 is a boundary. -/
theorem boundary187 : TopFiberBoundary 0x200200000000240f80380188008008001000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000240f80380188008008001000006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete187 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert187).beta ∈
      (AffineBoundaryCached.cert187).seeds.map Prod.fst := by
    rw [census187]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert187) 180 512
    2 AffineBoundaryCached.sheets187 AffineBoundaryCached.shadows187
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt187
    (AffineBoundaryCached.checked187) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census188 : (AffineBoundaryCached.cert188).seeds.map Prod.fst = AffineSearchData.allowed188 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 188 is a boundary. -/
theorem boundary188 : TopFiberBoundary 0x200200000000480640280190028008001000005003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000480640280190028008001000005003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete188 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert188).beta ∈
      (AffineBoundaryCached.cert188).seeds.map Prod.fst := by
    rw [census188]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert188) 180 512
    8 AffineBoundaryCached.sheets188 AffineBoundaryCached.shadows188
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt188
    (AffineBoundaryCached.checked188) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census189 : (AffineBoundaryCached.cert189).seeds.map Prod.fst = AffineSearchData.allowed189 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 189 is a boundary. -/
theorem boundary189 : TopFiberBoundary 0x200200000000480f40380190008008001000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000480f40380190008008001000005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete189 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert189).beta ∈
      (AffineBoundaryCached.cert189).seeds.map Prod.fst := by
    rw [census189]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert189) 180 512
    2 AffineBoundaryCached.sheets189 AffineBoundaryCached.shadows189
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt189
    (AffineBoundaryCached.checked189) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census190 : (AffineBoundaryCached.cert190).seeds.map Prod.fst = AffineSearchData.allowed190 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 190 is a boundary. -/
theorem boundary190 : TopFiberBoundary 0x200200000000900ec03801a0008008001000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200000000900ec03801a0008008001000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete190 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert190).beta ∈
      (AffineBoundaryCached.cert190).seeds.map Prod.fst := by
    rw [census190]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert190) 180 512
    2 AffineBoundaryCached.sheets190 AffineBoundaryCached.shadows190
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt190
    (AffineBoundaryCached.checked190) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census191 : (AffineBoundaryCached.cert191).seeds.map Prod.fst = AffineSearchData.allowed191 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 191 is a boundary. -/
theorem boundary191 : TopFiberBoundary 0x2004800800006c0088070028001004000000403000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2004800800006c0088070028001004000000403000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete191 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert191).beta ∈
      (AffineBoundaryCached.cert191).seeds.map Prod.fst := by
    rw [census191]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert191) 180 512
    8 AffineBoundaryCached.sheets191 AffineBoundaryCached.shadows191
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt191
    (AffineBoundaryCached.checked191) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census192 : (AffineBoundaryCached.cert192).seeds.map Prod.fst = AffineSearchData.allowed192 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 192 is a boundary. -/
theorem boundary192 : TopFiberBoundary 0x200480080000fc0188070008001004000000400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200480080000fc0188070008001004000000400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete192 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert192).beta ∈
      (AffineBoundaryCached.cert192).seeds.map Prod.fst := by
    rw [census192]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert192) 180 512
    2 AffineBoundaryCached.sheets192 AffineBoundaryCached.shadows192
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt192
    (AffineBoundaryCached.checked192) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census193 : (AffineBoundaryCached.cert193).seeds.map Prod.fst = AffineSearchData.allowed193 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 193 is a boundary. -/
theorem boundary193 : TopFiberBoundary 0x2009001000006c0088070028001002000000803000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2009001000006c0088070028001002000000803000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete193 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert193).beta ∈
      (AffineBoundaryCached.cert193).seeds.map Prod.fst := by
    rw [census193]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert193) 180 512
    8 AffineBoundaryCached.sheets193 AffineBoundaryCached.shadows193
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt193
    (AffineBoundaryCached.checked193) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census194 : (AffineBoundaryCached.cert194).seeds.map Prod.fst = AffineSearchData.allowed194 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 194 is a boundary. -/
theorem boundary194 : TopFiberBoundary 0x200900100000fc0188070008001002000000800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200900100000fc0188070008001002000000800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete194 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert194).beta ∈
      (AffineBoundaryCached.cert194).seeds.map Prod.fst := by
    rw [census194]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert194) 180 512
    2 AffineBoundaryCached.sheets194 AffineBoundaryCached.shadows194
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt194
    (AffineBoundaryCached.checked194) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census195 : (AffineBoundaryCached.cert195).seeds.map Prod.fst = AffineSearchData.allowed195 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 195 is a boundary. -/
theorem boundary195 : TopFiberBoundary 0x200dc01c0000000000240180030008001000e00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200dc01c0000000000240180030008001000e00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete195 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert195).beta ∈
      (AffineBoundaryCached.cert195).seeds.map Prod.fst := by
    rw [census195]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert195) 180 512
    6 AffineBoundaryCached.sheets195 AffineBoundaryCached.shadows195
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt195
    (AffineBoundaryCached.checked195) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census196 : (AffineBoundaryCached.cert196).seeds.map Prod.fst = AffineSearchData.allowed196 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 196 is a boundary. -/
theorem boundary196 : TopFiberBoundary 0x2010002000000006c0280180028038001001000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2010002000000006c0280180028038001001000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete196 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert196).beta ∈
      (AffineBoundaryCached.cert196).seeds.map Prod.fst := by
    rw [census196]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert196) 180 512
    8 AffineBoundaryCached.sheets196 AffineBoundaryCached.shadows196
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt196
    (AffineBoundaryCached.checked196) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census197 : (AffineBoundaryCached.cert197).seeds.map Prod.fst = AffineSearchData.allowed197 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 197 is a boundary. -/
theorem boundary197 : TopFiberBoundary 0x201000200000000fc0380180008038001001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x201000200000000fc0380180008038001001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete197 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert197).beta ∈
      (AffineBoundaryCached.cert197).seeds.map Prod.fst := by
    rw [census197]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert197) 180 512
    2 AffineBoundaryCached.sheets197 AffineBoundaryCached.shadows197
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt197
    (AffineBoundaryCached.checked197) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census198 : (AffineBoundaryCached.cert198).seeds.map Prod.fst = AffineSearchData.allowed198 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 198 is a boundary. -/
theorem boundary198 : TopFiberBoundary 0x2026004000000006c0280180028020001002000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2026004000000006c0280180028020001002000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete198 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert198).beta ∈
      (AffineBoundaryCached.cert198).seeds.map Prod.fst := by
    rw [census198]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert198) 180 512
    8 AffineBoundaryCached.sheets198 AffineBoundaryCached.shadows198
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt198
    (AffineBoundaryCached.checked198) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census199 : (AffineBoundaryCached.cert199).seeds.map Prod.fst = AffineSearchData.allowed199 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 199 is a boundary. -/
theorem boundary199 : TopFiberBoundary 0x202600400000000fc0380180008020001002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x202600400000000fc0380180008020001002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete199 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert199).beta ∈
      (AffineBoundaryCached.cert199).seeds.map Prod.fst := by
    rw [census199]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert199) 180 512
    2 AffineBoundaryCached.sheets199 AffineBoundaryCached.shadows199
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt199
    (AffineBoundaryCached.checked199) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census200 : (AffineBoundaryCached.cert200).seeds.map Prod.fst = AffineSearchData.allowed200 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 200 is a boundary. -/
theorem boundary200 : TopFiberBoundary 0x204140940000000000240180030015001004a00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x204140940000000000240180030015001004a00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete200 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert200).beta ∈
      (AffineBoundaryCached.cert200).seeds.map Prod.fst := by
    rw [census200]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert200) 180 512
    10 AffineBoundaryCached.sheets200 AffineBoundaryCached.shadows200
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt200
    (AffineBoundaryCached.checked200) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census201 : (AffineBoundaryCached.cert201).seeds.map Prod.fst = AffineSearchData.allowed201 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 201 is a boundary. -/
theorem boundary201 : TopFiberBoundary 0x204a008000000006c0280180028010001004000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x204a008000000006c0280180028010001004000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete201 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert201).beta ∈
      (AffineBoundaryCached.cert201).seeds.map Prod.fst := by
    rw [census201]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert201) 180 512
    8 AffineBoundaryCached.sheets201 AffineBoundaryCached.shadows201
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt201
    (AffineBoundaryCached.checked201) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census202 : (AffineBoundaryCached.cert202).seeds.map Prod.fst = AffineSearchData.allowed202 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 202 is a boundary. -/
theorem boundary202 : TopFiberBoundary 0x204a00800000000fc0380180008010001004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x204a00800000000fc0380180008010001004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete202 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert202).beta ∈
      (AffineBoundaryCached.cert202).seeds.map Prod.fst := by
    rw [census202]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert202) 180 512
    2 AffineBoundaryCached.sheets202 AffineBoundaryCached.shadows202
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt202
    (AffineBoundaryCached.checked202) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census203 : (AffineBoundaryCached.cert203).seeds.map Prod.fst = AffineSearchData.allowed203 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 203 is a boundary. -/
theorem boundary203 : TopFiberBoundary 0x205100b00000000000240180030023001005800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x205100b00000000000240180030023001005800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete203 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert203).beta ∈
      (AffineBoundaryCached.cert203).seeds.map Prod.fst := by
    rw [census203]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert203) 180 512
    8 AffineBoundaryCached.sheets203 AffineBoundaryCached.shadows203
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt203
    (AffineBoundaryCached.checked203) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty

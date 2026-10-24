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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart3
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census304 : (AffineBoundaryCached.cert304).seeds.map Prod.fst = AffineSearchData.allowed304 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 304 is a boundary. -/
theorem boundary304 : TopFiberBoundary 0xfc01c0208000008000001000000000006200c00240 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0208000008000001000000000006200c00240)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete304 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert304).beta ∈
      (AffineBoundaryCached.cert304).seeds.map Prod.fst := by
    rw [census304]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert304) 180 512
    4 AffineBoundaryCached.sheets304 AffineBoundaryCached.shadows304
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt304
    (AffineBoundaryCached.checked304) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census305 : (AffineBoundaryCached.cert305).seeds.map Prod.fst = AffineSearchData.allowed305 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 305 is a boundary. -/
theorem boundary305 : TopFiberBoundary 0xfc02a0060000000000000000000006600e00300000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc02a0060000000000000000000006600e00300000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete305 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert305).beta ∈
      (AffineBoundaryCached.cert305).seeds.map Prod.fst := by
    rw [census305]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert305) 180 512
    6 AffineBoundaryCached.sheets305 AffineBoundaryCached.shadows305
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt305
    (AffineBoundaryCached.checked305) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census306 : (AffineBoundaryCached.cert306).seeds.map Prod.fst = AffineSearchData.allowed306 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 306 is a boundary. -/
theorem boundary306 : TopFiberBoundary 0xfc0310050000000000000000000006a00e00280000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc0310050000000000000000000006a00e00280000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete306 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert306).beta ∈
      (AffineBoundaryCached.cert306).seeds.map Prod.fst := by
    rw [census306]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert306) 180 512
    6 AffineBoundaryCached.sheets306 AffineBoundaryCached.shadows306
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt306
    (AffineBoundaryCached.checked306) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census307 : (AffineBoundaryCached.cert307).seeds.map Prod.fst = AffineSearchData.allowed307 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 307 is a boundary. -/
theorem boundary307 : TopFiberBoundary 0x100000000000000ee01c401803c0008000000000180 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100000000000000ee01c401803c0008000000000180)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete307 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert307).beta ∈
      (AffineBoundaryCached.cert307).seeds.map Prod.fst := by
    rw [census307]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert307) 180 512
    6 AffineBoundaryCached.sheets307 AffineBoundaryCached.shadows307
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt307
    (AffineBoundaryCached.checked307) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census308 : (AffineBoundaryCached.cert308).seeds.map Prod.fst = AffineSearchData.allowed308 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 308 is a boundary. -/
theorem boundary308 : TopFiberBoundary 0x1000000000000015e02c401805c0008000000000140 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000000015e02c401805c0008000000000140)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete308 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert308).beta ∈
      (AffineBoundaryCached.cert308).seeds.map Prod.fst := by
    rw [census308]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert308) 180 512
    6 AffineBoundaryCached.sheets308 AffineBoundaryCached.shadows308
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt308
    (AffineBoundaryCached.checked308) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census309 : (AffineBoundaryCached.cert309).seeds.map Prod.fst = AffineSearchData.allowed309 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 309 is a boundary. -/
theorem boundary309 : TopFiberBoundary 0x1000000000000023e04c401809c00080000000000c0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000000023e04c401809c00080000000000c0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete309 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert309).beta ∈
      (AffineBoundaryCached.cert309).seeds.map Prod.fst := by
    rw [census309]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert309) 180 512
    6 AffineBoundaryCached.sheets309 AffineBoundaryCached.shadows309
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt309
    (AffineBoundaryCached.checked309) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census310 : (AffineBoundaryCached.cert310).seeds.map Prod.fst = AffineSearchData.allowed310 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 310 is a boundary. -/
theorem boundary310 : TopFiberBoundary 0x100000000000003e207040180e40008000000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100000000000003e207040180e40008000000000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete310 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert310).beta ∈
      (AffineBoundaryCached.cert310).seeds.map Prod.fst := by
    rw [census310]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert310) 180 512
    6 AffineBoundaryCached.sheets310 AffineBoundaryCached.shadows310
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt310
    (AffineBoundaryCached.checked310) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census311 : (AffineBoundaryCached.cert311).seeds.map Prod.fst = AffineSearchData.allowed311 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 311 is a boundary. -/
theorem boundary311 : TopFiberBoundary 0x1000000000000240f80380188038008000000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000000240f80380188038008000000006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete311 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert311).beta ∈
      (AffineBoundaryCached.cert311).seeds.map Prod.fst := by
    rw [census311]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert311) 180 512
    6 AffineBoundaryCached.sheets311 AffineBoundaryCached.shadows311
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt311
    (AffineBoundaryCached.checked311) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census312 : (AffineBoundaryCached.cert312).seeds.map Prod.fst = AffineSearchData.allowed312 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 312 is a boundary. -/
theorem boundary312 : TopFiberBoundary 0x1000000000000480f40380190038008000000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000000480f40380190038008000000005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete312 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert312).beta ∈
      (AffineBoundaryCached.cert312).seeds.map Prod.fst := by
    rw [census312]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert312) 180 512
    6 AffineBoundaryCached.sheets312 AffineBoundaryCached.shadows312
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt312
    (AffineBoundaryCached.checked312) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census313 : (AffineBoundaryCached.cert313).seeds.map Prod.fst = AffineSearchData.allowed313 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 313 is a boundary. -/
theorem boundary313 : TopFiberBoundary 0x1000000000000900ec03801a0038008000000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000000900ec03801a0038008000000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete313 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert313).beta ∈
      (AffineBoundaryCached.cert313).seeds.map Prod.fst := by
    rw [census313]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert313) 180 512
    6 AffineBoundaryCached.sheets313 AffineBoundaryCached.shadows313
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt313
    (AffineBoundaryCached.checked313) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census314 : (AffineBoundaryCached.cert314).seeds.map Prod.fst = AffineSearchData.allowed314 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 314 is a boundary. -/
theorem boundary314 : TopFiberBoundary 0x1000000000001200dc03801c0038008000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000001200dc03801c0038008000000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete314 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert314).beta ∈
      (AffineBoundaryCached.cert314).seeds.map Prod.fst := by
    rw [census314]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert314) 180 512
    6 AffineBoundaryCached.sheets314 AffineBoundaryCached.shadows314
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt314
    (AffineBoundaryCached.checked314) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census315 : (AffineBoundaryCached.cert315).seeds.map Prod.fst = AffineSearchData.allowed315 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 315 is a boundary. -/
theorem boundary315 : TopFiberBoundary 0x1000000000001207c00c401c01c0008000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000001207c00c401c01c0008000000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete315 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert315).beta ∈
      (AffineBoundaryCached.cert315).seeds.map Prod.fst := by
    rw [census315]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert315) 180 512
    6 AffineBoundaryCached.sheets315 AffineBoundaryCached.shadows315
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt315
    (AffineBoundaryCached.checked315) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census316 : (AffineBoundaryCached.cert316).seeds.map Prod.fst = AffineSearchData.allowed316 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 316 is a boundary. -/
theorem boundary316 : TopFiberBoundary 0x1000000000002080b4038011003800800000002d000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000002080b4038011003800800000002d000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete316 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert316).beta ∈
      (AffineBoundaryCached.cert316).seeds.map Prod.fst := by
    rw [census316]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert316) 180 512
    2 AffineBoundaryCached.sheets316 AffineBoundaryCached.shadows316
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt316
    (AffineBoundaryCached.checked316) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census317 : (AffineBoundaryCached.cert317).seeds.map Prod.fst = AffineSearchData.allowed317 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 317 is a boundary. -/
theorem boundary317 : TopFiberBoundary 0x10000000000020832804401100c000800000002d018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000020832804401100c000800000002d018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete317 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert317).beta ∈
      (AffineBoundaryCached.cert317).seeds.map Prod.fst := by
    rw [census317]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert317) 180 512
    8 AffineBoundaryCached.sheets317 AffineBoundaryCached.shadows317
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt317
    (AffineBoundaryCached.checked317) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census318 : (AffineBoundaryCached.cert318).seeds.map Prod.fst = AffineSearchData.allowed318 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 318 is a boundary. -/
theorem boundary318 : TopFiberBoundary 0x10000000000024019c0180100078008000000028030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000024019c0180100078008000000028030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete318 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert318).beta ∈
      (AffineBoundaryCached.cert318).seeds.map Prod.fst := by
    rw [census318]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert318) 180 512
    2 AffineBoundaryCached.sheets318 AffineBoundaryCached.shadows318
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt318
    (AffineBoundaryCached.checked318) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census319 : (AffineBoundaryCached.cert319).seeds.map Prod.fst = AffineSearchData.allowed319 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 319 is a boundary. -/
theorem boundary319 : TopFiberBoundary 0x100000000000240a2014401002c0008000000028198 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100000000000240a2014401002c0008000000028198)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete319 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert319).beta ∈
      (AffineBoundaryCached.cert319).seeds.map Prod.fst := by
    rw [census319]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert319) 180 512
    8 AffineBoundaryCached.sheets319 AffineBoundaryCached.shadows319
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt319
    (AffineBoundaryCached.checked319) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census320 : (AffineBoundaryCached.cert320).seeds.map Prod.fst = AffineSearchData.allowed320 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 320 is a boundary. -/
theorem boundary320 : TopFiberBoundary 0x10000000000024112024401004c0008000000028158 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000024112024401004c0008000000028158)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete320 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert320).beta ∈
      (AffineBoundaryCached.cert320).seeds.map Prod.fst := by
    rw [census320]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert320) 180 512
    8 AffineBoundaryCached.sheets320 AffineBoundaryCached.shadows320
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt320
    (AffineBoundaryCached.checked320) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census321 : (AffineBoundaryCached.cert321).seeds.map Prod.fst = AffineSearchData.allowed321 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 321 is a boundary. -/
theorem boundary321 : TopFiberBoundary 0x100000000000264028028010801800800000002e003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100000000000264028028010801800800000002e003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete321 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert321).beta ∈
      (AffineBoundaryCached.cert321).seeds.map Prod.fst := by
    rw [census321]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert321) 180 512
    8 AffineBoundaryCached.sheets321 AffineBoundaryCached.shadows321
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt321
    (AffineBoundaryCached.checked321) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census322 : (AffineBoundaryCached.cert322).seeds.map Prod.fst = AffineSearchData.allowed322 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 322 is a boundary. -/
theorem boundary322 : TopFiberBoundary 0x1000000000002bc05c0240138000008000000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000002bc05c0240138000008000000028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete322 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert322).beta ∈
      (AffineBoundaryCached.cert322).seeds.map Prod.fst := by
    rw [census322]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert322) 180 512
    6 AffineBoundaryCached.sheets322 AffineBoundaryCached.shadows322
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt322
    (AffineBoundaryCached.checked322) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census323 : (AffineBoundaryCached.cert323).seeds.map Prod.fst = AffineSearchData.allowed323 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 323 is a boundary. -/
theorem boundary323 : TopFiberBoundary 0x1000000000003600d40300140028008000000018005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000003600d40300140028008000000018005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete323 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert323).beta ∈
      (AffineBoundaryCached.cert323).seeds.map Prod.fst := by
    rw [census323]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert323) 180 512
    8 AffineBoundaryCached.sheets323 AffineBoundaryCached.shadows323
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt323
    (AffineBoundaryCached.checked323) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census324 : (AffineBoundaryCached.cert324).seeds.map Prod.fst = AffineSearchData.allowed324 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 324 is a boundary. -/
theorem boundary324 : TopFiberBoundary 0x10000000000036010800c0140050008000000018035 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000036010800c0140050008000000018035)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete324 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert324).beta ∈
      (AffineBoundaryCached.cert324).seeds.map Prod.fst := by
    rw [census324]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert324) 180 512
    8 AffineBoundaryCached.sheets324 AffineBoundaryCached.shadows324
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt324
    (AffineBoundaryCached.checked324) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census325 : (AffineBoundaryCached.cert325).seeds.map Prod.fst = AffineSearchData.allowed325 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 325 is a boundary. -/
theorem boundary325 : TopFiberBoundary 0x10000000000036084010401402400080000000181b0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000036084010401402400080000000181b0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete325 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert325).beta ∈
      (AffineBoundaryCached.cert325).seeds.map Prod.fst := by
    rw [census325]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert325) 180 512
    8 AffineBoundaryCached.sheets325 AffineBoundaryCached.shadows325
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt325
    (AffineBoundaryCached.checked325) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census326 : (AffineBoundaryCached.cert326).seeds.map Prod.fst = AffineSearchData.allowed326 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 326 is a boundary. -/
theorem boundary326 : TopFiberBoundary 0x10000000000041006c03800a003800800000001b000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000041006c03800a003800800000001b000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete326 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert326).beta ∈
      (AffineBoundaryCached.cert326).seeds.map Prod.fst := by
    rw [census326]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert326) 180 512
    4 AffineBoundaryCached.sheets326 AffineBoundaryCached.shadows326
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt326
    (AffineBoundaryCached.checked326) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census327 : (AffineBoundaryCached.cert327).seeds.map Prod.fst = AffineSearchData.allowed327 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 327 is a boundary. -/
theorem boundary327 : TopFiberBoundary 0x10000000000047c09c02400b8000008000000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000047c09c02400b8000008000000018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete327 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert327).beta ∈
      (AffineBoundaryCached.cert327).seeds.map Prod.fst := by
    rw [census327]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert327) 180 512
    6 AffineBoundaryCached.sheets327 AffineBoundaryCached.shadows327
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt327
    (AffineBoundaryCached.checked327) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census328 : (AffineBoundaryCached.cert328).seeds.map Prod.fst = AffineSearchData.allowed328 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 328 is a boundary. -/
theorem boundary328 : TopFiberBoundary 0x10000000000048015c0180080078008000000018030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000048015c0180080078008000000018030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete328 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert328).beta ∈
      (AffineBoundaryCached.cert328).seeds.map Prod.fst := by
    rw [census328]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert328) 180 512
    4 AffineBoundaryCached.sheets328 AffineBoundaryCached.shadows328
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt328
    (AffineBoundaryCached.checked328) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census329 : (AffineBoundaryCached.cert329).seeds.map Prod.fst = AffineSearchData.allowed329 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 329 is a boundary. -/
theorem boundary329 : TopFiberBoundary 0x1000000000005a005c03800c0038008000000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000005a005c03800c0038008000000028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete329 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert329).beta ∈
      (AffineBoundaryCached.cert329).seeds.map Prod.fst := by
    rw [census329]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert329) 180 512
    4 AffineBoundaryCached.sheets329 AffineBoundaryCached.shadows329
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt329
    (AffineBoundaryCached.checked329) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census330 : (AffineBoundaryCached.cert330).seeds.map Prod.fst = AffineSearchData.allowed330 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 330 is a boundary. -/
theorem boundary330 : TopFiberBoundary 0x1000000000005a07400c400c01c0008000000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000005a07400c400c01c0008000000028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete330 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert330).beta ∈
      (AffineBoundaryCached.cert330).seeds.map Prod.fst := by
    rw [census330]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert330) 180 512
    4 AffineBoundaryCached.sheets330 AffineBoundaryCached.shadows330
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt330
    (AffineBoundaryCached.checked330) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census331 : (AffineBoundaryCached.cert331).seeds.map Prod.fst = AffineSearchData.allowed331 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 331 is a boundary. -/
theorem boundary331 : TopFiberBoundary 0x1000000000006180240380030038008000000036000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006180240380030038008000000036000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete331 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert331).beta ∈
      (AffineBoundaryCached.cert331).seeds.map Prod.fst := by
    rw [census331]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert331) 180 512
    2 AffineBoundaryCached.sheets331 AffineBoundaryCached.shadows331
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt331
    (AffineBoundaryCached.checked331) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census332 : (AffineBoundaryCached.cert332).seeds.map Prod.fst = AffineSearchData.allowed332 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 332 is a boundary. -/
theorem boundary332 : TopFiberBoundary 0x10000000000063c0dc0240038000008000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000063c0dc0240038000008000000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete332 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert332).beta ∈
      (AffineBoundaryCached.cert332).seeds.map Prod.fst := by
    rw [census332]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert332) 180 512
    4 AffineBoundaryCached.sheets332 AffineBoundaryCached.shadows332
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt332
    (AffineBoundaryCached.checked332) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census333 : (AffineBoundaryCached.cert333).seeds.map Prod.fst = AffineSearchData.allowed333 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 333 is a boundary. -/
theorem boundary333 : TopFiberBoundary 0x10000000000065002c0380020038008000000033000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000065002c0380020038008000000033000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete333 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert333).beta ∈
      (AffineBoundaryCached.cert333).seeds.map Prod.fst := by
    rw [census333]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert333) 180 512
    2 AffineBoundaryCached.sheets333 AffineBoundaryCached.shadows333
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt333
    (AffineBoundaryCached.checked333) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census334 : (AffineBoundaryCached.cert334).seeds.map Prod.fst = AffineSearchData.allowed334 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 334 is a boundary. -/
theorem boundary334 : TopFiberBoundary 0x1000000000006880340380010038008000000035000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006880340380010038008000000035000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete334 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert334).beta ∈
      (AffineBoundaryCached.cert334).seeds.map Prod.fst := by
    rw [census334]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert334) 180 512
    2 AffineBoundaryCached.sheets334 AffineBoundaryCached.shadows334
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt334
    (AffineBoundaryCached.checked334) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census335 : (AffineBoundaryCached.cert335).seeds.map Prod.fst = AffineSearchData.allowed335 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 335 is a boundary. -/
theorem boundary335 : TopFiberBoundary 0x1000000000006880a40280010018008000000035003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006880a40280010018008000000035003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete335 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert335).beta ∈
      (AffineBoundaryCached.cert335).seeds.map Prod.fst := by
    rw [census335]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert335) 180 512
    4 AffineBoundaryCached.sheets335 AffineBoundaryCached.shadows335
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt335
    (AffineBoundaryCached.checked335) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census336 : (AffineBoundaryCached.cert336).seeds.map Prod.fst = AffineSearchData.allowed336 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 336 is a boundary. -/
theorem boundary336 : TopFiberBoundary 0x1000000000006c011c0180000078008000000030030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000006c011c0180000078008000000030030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete336 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert336).beta ∈
      (AffineBoundaryCached.cert336).seeds.map Prod.fst := by
    rw [census336]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert336) 180 512
    2 AffineBoundaryCached.sheets336 AffineBoundaryCached.shadows336
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt336
    (AffineBoundaryCached.checked336) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census337 : (AffineBoundaryCached.cert337).seeds.map Prod.fst = AffineSearchData.allowed337 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 337 is a boundary. -/
theorem boundary337 : TopFiberBoundary 0x1000000000007380f80240070000008000000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007380f80240070000008000000006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete337 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert337).beta ∈
      (AffineBoundaryCached.cert337).seeds.map Prod.fst := by
    rw [census337]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert337) 180 512
    4 AffineBoundaryCached.sheets337 AffineBoundaryCached.shadows337
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt337
    (AffineBoundaryCached.checked337) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census338 : (AffineBoundaryCached.cert338).seeds.map Prod.fst = AffineSearchData.allowed338 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 338 is a boundary. -/
theorem boundary338 : TopFiberBoundary 0x1000000000007540f40240068000008000000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007540f40240068000008000000005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete338 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert338).beta ∈
      (AffineBoundaryCached.cert338).seeds.map Prod.fst := by
    rw [census338]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert338) 180 512
    2 AffineBoundaryCached.sheets338 AffineBoundaryCached.shadows338
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt338
    (AffineBoundaryCached.checked338) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census339 : (AffineBoundaryCached.cert339).seeds.map Prod.fst = AffineSearchData.allowed339 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 339 is a boundary. -/
theorem boundary339 : TopFiberBoundary 0x1000000000007700440300060028008000000003005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007700440300060028008000000003005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete339 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert339).beta ∈
      (AffineBoundaryCached.cert339).seeds.map Prod.fst := by
    rw [census339]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert339) 180 512
    2 AffineBoundaryCached.sheets339 AffineBoundaryCached.shadows339
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt339
    (AffineBoundaryCached.checked339) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census340 : (AffineBoundaryCached.cert340).seeds.map Prod.fst = AffineSearchData.allowed340 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 340 is a boundary. -/
theorem boundary340 : TopFiberBoundary 0x10000000000078c0ec0240058000008000000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000000000078c0ec0240058000008000000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete340 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert340).beta ∈
      (AffineBoundaryCached.cert340).seeds.map Prod.fst := by
    rw [census340]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert340) 180 512
    2 AffineBoundaryCached.sheets340 AffineBoundaryCached.shadows340
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt340
    (AffineBoundaryCached.checked340) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census341 : (AffineBoundaryCached.cert341).seeds.map Prod.fst = AffineSearchData.allowed341 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 341 is a boundary. -/
theorem boundary341 : TopFiberBoundary 0x1000000000007c40500300048028008000000006005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007c40500300048028008000000006005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete341 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert341).beta ∈
      (AffineBoundaryCached.cert341).seeds.map Prod.fst := by
    rw [census341]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert341) 180 512
    2 AffineBoundaryCached.sheets341 AffineBoundaryCached.shadows341
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt341
    (AffineBoundaryCached.checked341) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census342 : (AffineBoundaryCached.cert342).seeds.map Prod.fst = AffineSearchData.allowed342 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 342 is a boundary. -/
theorem boundary342 : TopFiberBoundary 0x1000000000007e01500140040060008000000000033 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e01500140040060008000000000033)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete342 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert342).beta ∈
      (AffineBoundaryCached.cert342).seeds.map Prod.fst := by
    rw [census342]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert342) 180 512
    2 AffineBoundaryCached.sheets342 AffineBoundaryCached.shadows342
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt342
    (AffineBoundaryCached.checked342) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census343 : (AffineBoundaryCached.cert343).seeds.map Prod.fst = AffineSearchData.allowed343 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 343 is a boundary. -/
theorem boundary343 : TopFiberBoundary 0x1000000000007e018800c0040050008000000000035 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e018800c0040050008000000000035)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete343 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert343).beta ∈
      (AffineBoundaryCached.cert343).seeds.map Prod.fst := by
    rw [census343]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert343) 180 512
    2 AffineBoundaryCached.sheets343 AffineBoundaryCached.shadows343
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt343
    (AffineBoundaryCached.checked343) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census344 : (AffineBoundaryCached.cert344).seeds.map Prod.fst = AffineSearchData.allowed344 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 344 is a boundary. -/
theorem boundary344 : TopFiberBoundary 0x1000000000007e06200e40040180008000000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e06200e40040180008000000000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete344 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert344).beta ∈
      (AffineBoundaryCached.cert344).seeds.map Prod.fst := by
    rw [census344]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert344) 180 512
    4 AffineBoundaryCached.sheets344 AffineBoundaryCached.shadows344
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt344
    (AffineBoundaryCached.checked344) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census345 : (AffineBoundaryCached.cert345).seeds.map Prod.fst = AffineSearchData.allowed345 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 345 is a boundary. -/
theorem boundary345 : TopFiberBoundary 0x1000000000007e08c010400402400080000000001b0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e08c010400402400080000000001b0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete345 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert345).beta ∈
      (AffineBoundaryCached.cert345).seeds.map Prod.fst := by
    rw [census345]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert345) 180 512
    2 AffineBoundaryCached.sheets345 AffineBoundaryCached.shadows345
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt345
    (AffineBoundaryCached.checked345) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census346 : (AffineBoundaryCached.cert346).seeds.map Prod.fst = AffineSearchData.allowed346 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 346 is a boundary. -/
theorem boundary346 : TopFiberBoundary 0x1000000000007e09e01240040200008000000000180 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e09e01240040200008000000000180)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete346 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert346).beta ∈
      (AffineBoundaryCached.cert346).seeds.map Prod.fst := by
    rw [census346]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert346) 180 512
    8 AffineBoundaryCached.sheets346 AffineBoundaryCached.shadows346
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt346
    (AffineBoundaryCached.checked346) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census347 : (AffineBoundaryCached.cert347).seeds.map Prod.fst = AffineSearchData.allowed347 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 347 is a boundary. -/
theorem boundary347 : TopFiberBoundary 0x1000000000007e12e02240040400008000000000140 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e12e02240040400008000000000140)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete347 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert347).beta ∈
      (AffineBoundaryCached.cert347).seeds.map Prod.fst := by
    rw [census347]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert347) 180 512
    8 AffineBoundaryCached.sheets347 AffineBoundaryCached.shadows347
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt347
    (AffineBoundaryCached.checked347) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census348 : (AffineBoundaryCached.cert348).seeds.map Prod.fst = AffineSearchData.allowed348 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 348 is a boundary. -/
theorem boundary348 : TopFiberBoundary 0x1000000000007e24e042400408000080000000000c0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e24e042400408000080000000000c0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete348 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert348).beta ∈
      (AffineBoundaryCached.cert348).seeds.map Prod.fst := by
    rw [census348]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert348) 180 512
    8 AffineBoundaryCached.sheets348 AffineBoundaryCached.shadows348
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt348
    (AffineBoundaryCached.checked348) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census349 : (AffineBoundaryCached.cert349).seeds.map Prod.fst = AffineSearchData.allowed349 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 349 is a boundary. -/
theorem boundary349 : TopFiberBoundary 0x1000000000007e48e08240041000008000000000c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e48e08240041000008000000000c00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete349 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert349).beta ∈
      (AffineBoundaryCached.cert349).seeds.map Prod.fst := by
    rw [census349]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert349) 180 512
    8 AffineBoundaryCached.sheets349 AffineBoundaryCached.shadows349
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt349
    (AffineBoundaryCached.checked349) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census350 : (AffineBoundaryCached.cert350).seeds.map Prod.fst = AffineSearchData.allowed350 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 350 is a boundary. -/
theorem boundary350 : TopFiberBoundary 0x1000000000007e90e10240042000008000000000a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007e90e10240042000008000000000a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete350 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert350).beta ∈
      (AffineBoundaryCached.cert350).seeds.map Prod.fst := by
    rw [census350]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert350) 180 512
    8 AffineBoundaryCached.sheets350 AffineBoundaryCached.shadows350
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt350
    (AffineBoundaryCached.checked350) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census351 : (AffineBoundaryCached.cert351).seeds.map Prod.fst = AffineSearchData.allowed351 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 351 is a boundary. -/
theorem boundary351 : TopFiberBoundary 0x1000000000007f20e20240044000008000000000600 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000000000007f20e20240044000008000000000600)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete351 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert351).beta ∈
      (AffineBoundaryCached.cert351).seeds.map Prod.fst := by
    rw [census351]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert351) 180 512
    8 AffineBoundaryCached.sheets351 AffineBoundaryCached.shadows351
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt351
    (AffineBoundaryCached.checked351) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census352 : (AffineBoundaryCached.cert352).seeds.map Prod.fst = AffineSearchData.allowed352 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 352 is a boundary. -/
theorem boundary352 : TopFiberBoundary 0x1000012010001600600240140000008140140008010 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000012010001600600240140000008140140008010)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete352 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert352).beta ∈
      (AffineBoundaryCached.cert352).seeds.map Prod.fst := by
    rw [census352]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert352) 180 512
    8 AffineBoundaryCached.sheets352 AffineBoundaryCached.shadows352
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt352
    (AffineBoundaryCached.checked352) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census353 : (AffineBoundaryCached.cert353).seeds.map Prod.fst = AffineSearchData.allowed353 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 353 is a boundary. -/
theorem boundary353 : TopFiberBoundary 0x1000012010001601400040140040008140140008020 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000012010001601400040140040008140140008020)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete353 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert353).beta ∈
      (AffineBoundaryCached.cert353).seeds.map Prod.fst := by
    rw [census353]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert353) 180 512
    2 AffineBoundaryCached.sheets353 AffineBoundaryCached.shadows353
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt353
    (AffineBoundaryCached.checked353) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census354 : (AffineBoundaryCached.cert354).seeds.map Prod.fst = AffineSearchData.allowed354 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 354 is a boundary. -/
theorem boundary354 : TopFiberBoundary 0x1000020800006400c002400000000080d8018014004 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000020800006400c002400000000080d8018014004)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete354 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert354).beta ∈
      (AffineBoundaryCached.cert354).seeds.map Prod.fst := by
    rw [census354]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert354) 180 512
    4 AffineBoundaryCached.sheets354 AffineBoundaryCached.shadows354
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt354
    (AffineBoundaryCached.checked354) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census355 : (AffineBoundaryCached.cert355).seeds.map Prod.fst = AffineSearchData.allowed355 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 355 is a boundary. -/
theorem boundary355 : TopFiberBoundary 0x1000024020002c01e000400000400080c00c0010010 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000024020002c01e000400000400080c00c0010010)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete355 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert355).beta ∈
      (AffineBoundaryCached.cert355).seeds.map Prod.fst := by
    rw [census355]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert355) 180 512
    4 AffineBoundaryCached.sheets355 AffineBoundaryCached.shadows355
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt355
    (AffineBoundaryCached.checked355) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census356 : (AffineBoundaryCached.cert356).seeds.map Prod.fst = AffineSearchData.allowed356 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 356 is a boundary. -/
theorem boundary356 : TopFiberBoundary 0x1000024020002c028006400000800080c00c0010008 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000024020002c028006400000800080c00c0010008)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete356 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert356).beta ∈
      (AffineBoundaryCached.cert356).seeds.map Prod.fst := by
    rw [census356]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert356) 180 512
    2 AffineBoundaryCached.sheets356 AffineBoundaryCached.shadows356
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt356
    (AffineBoundaryCached.checked356) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census357 : (AffineBoundaryCached.cert357).seeds.map Prod.fst = AffineSearchData.allowed357 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 357 is a boundary. -/
theorem boundary357 : TopFiberBoundary 0x10000240200064016000401000400080c00c0008010 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10000240200064016000401000400080c00c0008010)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete357 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert357).beta ∈
      (AffineBoundaryCached.cert357).seeds.map Prod.fst := by
    rw [census357]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert357) 180 512
    10 AffineBoundaryCached.sheets357 AffineBoundaryCached.shadows357
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt357
    (AffineBoundaryCached.checked357) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census358 : (AffineBoundaryCached.cert358).seeds.map Prod.fst = AffineSearchData.allowed358 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 358 is a boundary. -/
theorem boundary358 : TopFiberBoundary 0x1000036030000c00c00240000000008180180000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000036030000c00c00240000000008180180000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete358 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert358).beta ∈
      (AffineBoundaryCached.cert358).seeds.map Prod.fst := by
    rw [census358]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert358) 180 512
    2 AffineBoundaryCached.sheets358 AffineBoundaryCached.shadows358
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt358
    (AffineBoundaryCached.checked358) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census359 : (AffineBoundaryCached.cert359).seeds.map Prod.fst = AffineSearchData.allowed359 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 359 is a boundary. -/
theorem boundary359 : TopFiberBoundary 0x1000036030000c01e00040000040008180180000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000036030000c01e00040000040008180180000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete359 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert359).beta ∈
      (AffineBoundaryCached.cert359).seeds.map Prod.fst := by
    rw [census359]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert359) 180 512
    2 AffineBoundaryCached.sheets359 AffineBoundaryCached.shadows359
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt359
    (AffineBoundaryCached.checked359) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census360 : (AffineBoundaryCached.cert360).seeds.map Prod.fst = AffineSearchData.allowed360 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 360 is a boundary. -/
theorem boundary360 : TopFiberBoundary 0x1000090010007e00e00240040000008a00000080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000090010007e00e00240040000008a00000080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete360 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert360).beta ∈
      (AffineBoundaryCached.cert360).seeds.map Prod.fst := by
    rw [census360]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert360) 180 512
    8 AffineBoundaryCached.sheets360 AffineBoundaryCached.shadows360
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt360
    (AffineBoundaryCached.checked360) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census361 : (AffineBoundaryCached.cert361).seeds.map Prod.fst = AffineSearchData.allowed361 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 361 is a boundary. -/
theorem boundary361 : TopFiberBoundary 0x1000120020007e00e00240040000008600000100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000120020007e00e00240040000008600000100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete361 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert361).beta ∈
      (AffineBoundaryCached.cert361).seeds.map Prod.fst := by
    rw [census361]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert361) 180 512
    8 AffineBoundaryCached.sheets361 AffineBoundaryCached.shadows361
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt361
    (AffineBoundaryCached.checked361) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census362 : (AffineBoundaryCached.cert362).seeds.map Prod.fst = AffineSearchData.allowed362 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 362 is a boundary. -/
theorem boundary362 : TopFiberBoundary 0x10002000000004806080b0020029001001000005003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10002000000004806080b0020029001001000005003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete362 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert362).beta ∈
      (AffineBoundaryCached.cert362).seeds.map Prod.fst := by
    rw [census362]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert362) 180 512
    2 AffineBoundaryCached.sheets362 AffineBoundaryCached.shadows362
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt362
    (AffineBoundaryCached.checked362) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census363 : (AffineBoundaryCached.cert363).seeds.map Prod.fst = AffineSearchData.allowed363 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 363 is a boundary. -/
theorem boundary363 : TopFiberBoundary 0x1000200000000480f081b0020009001001000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000200000000480f081b0020009001001000005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete363 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert363).beta ∈
      (AffineBoundaryCached.cert363).seeds.map Prod.fst := by
    rw [census363]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert363) 180 512
    2 AffineBoundaryCached.sheets363 AffineBoundaryCached.shadows363
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt363
    (AffineBoundaryCached.checked363) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census364 : (AffineBoundaryCached.cert364).seeds.map Prod.fst = AffineSearchData.allowed364 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 364 is a boundary. -/
theorem boundary364 : TopFiberBoundary 0x10002000000006c0088070028031001001000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10002000000006c0088070028031001001000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete364 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert364).beta ∈
      (AffineBoundaryCached.cert364).seeds.map Prod.fst := by
    rw [census364]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert364) 180 512
    8 AffineBoundaryCached.sheets364 AffineBoundaryCached.shadows364
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt364
    (AffineBoundaryCached.checked364) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census365 : (AffineBoundaryCached.cert365).seeds.map Prod.fst = AffineSearchData.allowed365 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 365 is a boundary. -/
theorem boundary365 : TopFiberBoundary 0x1000200000000900e881b0010009001001000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000200000000900e881b0010009001001000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete365 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert365).beta ∈
      (AffineBoundaryCached.cert365).seeds.map Prod.fst := by
    rw [census365]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert365) 180 512
    2 AffineBoundaryCached.sheets365 AffineBoundaryCached.shadows365
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt365
    (AffineBoundaryCached.checked365) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census366 : (AffineBoundaryCached.cert366).seeds.map Prod.fst = AffineSearchData.allowed366 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 366 is a boundary. -/
theorem boundary366 : TopFiberBoundary 0x1000200000000d80e081b0000009001001000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000200000000d80e081b0000009001001000006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete366 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert366).beta ∈
      (AffineBoundaryCached.cert366).seeds.map Prod.fst := by
    rw [census366]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert366) 180 512
    2 AffineBoundaryCached.sheets366 AffineBoundaryCached.shadows366
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt366
    (AffineBoundaryCached.checked366) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census367 : (AffineBoundaryCached.cert367).seeds.map Prod.fst = AffineSearchData.allowed367 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 367 is a boundary. -/
theorem boundary367 : TopFiberBoundary 0x1000200000000fc0188070008031001001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000200000000fc0188070008031001001000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete367 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert367).beta ∈
      (AffineBoundaryCached.cert367).seeds.map Prod.fst := by
    rw [census367]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert367) 180 512
    2 AffineBoundaryCached.sheets367 AffineBoundaryCached.shadows367
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt367
    (AffineBoundaryCached.checked367) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census368 : (AffineBoundaryCached.cert368).seeds.map Prod.fst = AffineSearchData.allowed368 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 368 is a boundary. -/
theorem boundary368 : TopFiberBoundary 0x1000480080007e00e0024004000000d000000400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000480080007e00e0024004000000d000000400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete368 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert368).beta ∈
      (AffineBoundaryCached.cert368).seeds.map Prod.fst := by
    rw [census368]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert368) 180 512
    8 AffineBoundaryCached.sheets368 AffineBoundaryCached.shadows368
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt368
    (AffineBoundaryCached.checked368) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census369 : (AffineBoundaryCached.cert369).seeds.map Prod.fst = AffineSearchData.allowed369 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 369 is a boundary. -/
theorem boundary369 : TopFiberBoundary 0x1000900100007e00e0024004000000b000000800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1000900100007e00e0024004000000b000000800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete369 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert369).beta ∈
      (AffineBoundaryCached.cert369).seeds.map Prod.fst := by
    rw [census369]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert369) 180 512
    8 AffineBoundaryCached.sheets369 AffineBoundaryCached.shadows369
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt369
    (AffineBoundaryCached.checked369) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census370 : (AffineBoundaryCached.cert370).seeds.map Prod.fst = AffineSearchData.allowed370 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 370 is a boundary. -/
theorem boundary370 : TopFiberBoundary 0x1001000000000003281480c0015004000800000001d := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001000000000003281480c0015004000800000001d)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete370 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert370).beta ∈
      (AffineBoundaryCached.cert370).seeds.map Prod.fst := by
    rw [census370]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert370) 180 512
    8 AffineBoundaryCached.sheets370 AffineBoundaryCached.shadows370
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt370
    (AffineBoundaryCached.checked370) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census371 : (AffineBoundaryCached.cert371).seeds.map Prod.fst = AffineSearchData.allowed371 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 371 is a boundary. -/
theorem boundary371 : TopFiberBoundary 0x1001000000000003441440c0014804000800000001e := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001000000000003441440c0014804000800000001e)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete371 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert371).beta ∈
      (AffineBoundaryCached.cert371).seeds.map Prod.fst := by
    rw [census371]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert371) 180 512
    8 AffineBoundaryCached.sheets371 AffineBoundaryCached.shadows371
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt371
    (AffineBoundaryCached.checked371) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census372 : (AffineBoundaryCached.cert372).seeds.map Prod.fst = AffineSearchData.allowed372 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 372 is a boundary. -/
theorem boundary372 : TopFiberBoundary 0x1001000000000007701d00c00060040008000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001000000000007701d00c00060040008000000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete372 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert372).beta ∈
      (AffineBoundaryCached.cert372).seeds.map Prod.fst := by
    rw [census372]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert372) 180 512
    2 AffineBoundaryCached.sheets372 AffineBoundaryCached.shadows372
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt372
    (AffineBoundaryCached.checked372) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census373 : (AffineBoundaryCached.cert373).seeds.map Prod.fst = AffineSearchData.allowed373 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 373 is a boundary. -/
theorem boundary373 : TopFiberBoundary 0x1001000000000007a81c80c00050040008000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001000000000007a81c80c00050040008000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete373 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert373).beta ∈
      (AffineBoundaryCached.cert373).seeds.map Prod.fst := by
    rw [census373]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert373) 180 512
    2 AffineBoundaryCached.sheets373 AffineBoundaryCached.shadows373
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt373
    (AffineBoundaryCached.checked373) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census374 : (AffineBoundaryCached.cert374).seeds.map Prod.fst = AffineSearchData.allowed374 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 374 is a boundary. -/
theorem boundary374 : TopFiberBoundary 0x1001000000000007c41c40c00048040008000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001000000000007c41c40c00048040008000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete374 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert374).beta ∈
      (AffineBoundaryCached.cert374).seeds.map Prod.fst := by
    rw [census374]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert374) 180 512
    2 AffineBoundaryCached.sheets374 AffineBoundaryCached.shadows374
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt374
    (AffineBoundaryCached.checked374) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census375 : (AffineBoundaryCached.cert375).seeds.map Prod.fst = AffineSearchData.allowed375 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 375 is a boundary. -/
theorem boundary375 : TopFiberBoundary 0x1001200200007e00e00240040000038000001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001200200007e00e00240040000038000001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete375 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert375).beta ∈
      (AffineBoundaryCached.cert375).seeds.map Prod.fst := by
    rw [census375]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert375) 180 512
    8 AffineBoundaryCached.sheets375 AffineBoundaryCached.shadows375
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt375
    (AffineBoundaryCached.checked375) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census376 : (AffineBoundaryCached.cert376).seeds.map Prod.fst = AffineSearchData.allowed376 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 376 is a boundary. -/
theorem boundary376 : TopFiberBoundary 0x10016006000000000022c0ac0140080010003000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10016006000000000022c0ac0140080010003000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete376 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert376).beta ∈
      (AffineBoundaryCached.cert376).seeds.map Prod.fst := by
    rw [census376]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert376) 180 512
    4 AffineBoundaryCached.sheets376 AffineBoundaryCached.shadows376
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt376
    (AffineBoundaryCached.checked376) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census377 : (AffineBoundaryCached.cert377).seeds.map Prod.fst = AffineSearchData.allowed377 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 377 is a boundary. -/
theorem boundary377 : TopFiberBoundary 0x1001a00a000000000043407400c0100020005000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1001a00a000000000043407400c0100020005000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete377 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert377).beta ∈
      (AffineBoundaryCached.cert377).seeds.map Prod.fst := by
    rw [census377]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert377) 180 512
    4 AffineBoundaryCached.sheets377 AffineBoundaryCached.shadows377
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt377
    (AffineBoundaryCached.checked377) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census378 : (AffineBoundaryCached.cert378).seeds.map Prod.fst = AffineSearchData.allowed378 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 378 is a boundary. -/
theorem boundary378 : TopFiberBoundary 0x10022002000000000032807400c00e0018001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10022002000000000032807400c00e0018001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete378 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert378).beta ∈
      (AffineBoundaryCached.cert378).seeds.map Prod.fst := by
    rw [census378]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert378) 180 512
    4 AffineBoundaryCached.sheets378 AffineBoundaryCached.shadows378
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt378
    (AffineBoundaryCached.checked378) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census379 : (AffineBoundaryCached.cert379).seeds.map Prod.fst = AffineSearchData.allowed379 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 379 is a boundary. -/
theorem boundary379 : TopFiberBoundary 0x1002400400000000fc0380180038020000002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1002400400000000fc0380180038020000002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete379 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert379).beta ∈
      (AffineBoundaryCached.cert379).seeds.map Prod.fst := by
    rw [census379]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert379) 180 512
    6 AffineBoundaryCached.sheets379 AffineBoundaryCached.shadows379
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt379
    (AffineBoundaryCached.checked379) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census380 : (AffineBoundaryCached.cert380).seeds.map Prod.fst = AffineSearchData.allowed380 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 380 is a boundary. -/
theorem boundary380 : TopFiberBoundary 0x1002400400000007e00c401801c0020000002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1002400400000007e00c401801c0020000002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete380 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert380).beta ∈
      (AffineBoundaryCached.cert380).seeds.map Prod.fst := by
    rw [census380]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert380) 180 512
    6 AffineBoundaryCached.sheets380 AffineBoundaryCached.shadows380
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt380
    (AffineBoundaryCached.checked380) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census381 : (AffineBoundaryCached.cert381).seeds.map Prod.fst = AffineSearchData.allowed381 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 381 is a boundary. -/
theorem boundary381 : TopFiberBoundary 0x10024004000024002c0280100018020000002028003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10024004000024002c0280100018020000002028003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete381 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert381).beta ∈
      (AffineBoundaryCached.cert381).seeds.map Prod.fst := by
    rw [census381]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert381) 180 512
    8 AffineBoundaryCached.sheets381 AffineBoundaryCached.shadows381
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt381
    (AffineBoundaryCached.checked381) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census382 : (AffineBoundaryCached.cert382).seeds.map Prod.fst = AffineSearchData.allowed382 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 382 is a boundary. -/
theorem boundary382 : TopFiberBoundary 0x10024004000024032004401000c0020000002028018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10024004000024032004401000c0020000002028018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete382 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert382).beta ∈
      (AffineBoundaryCached.cert382).seeds.map Prod.fst := by
    rw [census382]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert382) 180 512
    8 AffineBoundaryCached.sheets382 AffineBoundaryCached.shadows382
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt382
    (AffineBoundaryCached.checked382) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census383 : (AffineBoundaryCached.cert383).seeds.map Prod.fst = AffineSearchData.allowed383 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 383 is a boundary. -/
theorem boundary383 : TopFiberBoundary 0x1002400400003601400040140040020000002018030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1002400400003601400040140040020000002018030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete383 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert383).beta ∈
      (AffineBoundaryCached.cert383).seeds.map Prod.fst := by
    rw [census383]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert383) 180 512
    8 AffineBoundaryCached.sheets383 AffineBoundaryCached.shadows383
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt383
    (AffineBoundaryCached.checked383) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census384 : (AffineBoundaryCached.cert384).seeds.map Prod.fst = AffineSearchData.allowed384 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 384 is a boundary. -/
theorem boundary384 : TopFiberBoundary 0x1002400400007e01c00040040040020000002000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1002400400007e01c00040040040020000002000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete384 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert384).beta ∈
      (AffineBoundaryCached.cert384).seeds.map Prod.fst := by
    rw [census384]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert384) 180 512
    2 AffineBoundaryCached.sheets384 AffineBoundaryCached.shadows384
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt384
    (AffineBoundaryCached.checked384) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census385 : (AffineBoundaryCached.cert385).seeds.map Prod.fst = AffineSearchData.allowed385 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 385 is a boundary. -/
theorem boundary385 : TopFiberBoundary 0x10028008000000000063c0c001801a0030004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10028008000000000063c0c001801a0030004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete385 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert385).beta ∈
      (AffineBoundaryCached.cert385).seeds.map Prod.fst := by
    rw [census385]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert385) 180 512
    2 AffineBoundaryCached.sheets385 AffineBoundaryCached.shadows385
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt385
    (AffineBoundaryCached.checked385) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census386 : (AffineBoundaryCached.cert386).seeds.map Prod.fst = AffineSearchData.allowed386 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 386 is a boundary. -/
theorem boundary386 : TopFiberBoundary 0x1002bc05c0000000000240180000020000002e00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1002bc05c0000000000240180000020000002e00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete386 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert386).beta ∈
      (AffineBoundaryCached.cert386).seeds.map Prod.fst := by
    rw [census386]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert386) 180 512
    6 AffineBoundaryCached.sheets386 AffineBoundaryCached.shadows386
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt386
    (AffineBoundaryCached.checked386) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census387 : (AffineBoundaryCached.cert387).seeds.map Prod.fst = AffineSearchData.allowed387 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 387 is a boundary. -/
theorem boundary387 : TopFiberBoundary 0x1004000000000001044100740088128020000000036 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004000000000001044100740088128020000000036)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete387 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert387).beta ∈
      (AffineBoundaryCached.cert387).seeds.map Prod.fst := by
    rw [census387]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert387) 180 512
    4 AffineBoundaryCached.sheets387 AffineBoundaryCached.shadows387
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt387
    (AffineBoundaryCached.checked387) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census388 : (AffineBoundaryCached.cert388).seeds.map Prod.fst = AffineSearchData.allowed388 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 388 is a boundary. -/
theorem boundary388 : TopFiberBoundary 0x1004000000000003604540740000128020000000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004000000000003604540740000128020000000018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete388 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert388).beta ∈
      (AffineBoundaryCached.cert388).seeds.map Prod.fst := by
    rw [census388]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert388) 180 512
    4 AffineBoundaryCached.sheets388 AffineBoundaryCached.shadows388
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt388
    (AffineBoundaryCached.checked388) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census389 : (AffineBoundaryCached.cert389).seeds.map Prod.fst = AffineSearchData.allowed389 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 389 is a boundary. -/
theorem boundary389 : TopFiberBoundary 0x10047c09c0000000000240180000010000004e00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10047c09c0000000000240180000010000004e00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete389 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert389).beta ∈
      (AffineBoundaryCached.cert389).seeds.map Prod.fst := by
    rw [census389]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert389) 180 512
    6 AffineBoundaryCached.sheets389 AffineBoundaryCached.shadows389
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt389
    (AffineBoundaryCached.checked389) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census390 : (AffineBoundaryCached.cert390).seeds.map Prod.fst = AffineSearchData.allowed390 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 390 is a boundary. -/
theorem boundary390 : TopFiberBoundary 0x1004800800000000fc0380180038010000004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004800800000000fc0380180038010000004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete390 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert390).beta ∈
      (AffineBoundaryCached.cert390).seeds.map Prod.fst := by
    rw [census390]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert390) 180 512
    6 AffineBoundaryCached.sheets390 AffineBoundaryCached.shadows390
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt390
    (AffineBoundaryCached.checked390) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census391 : (AffineBoundaryCached.cert391).seeds.map Prod.fst = AffineSearchData.allowed391 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 391 is a boundary. -/
theorem boundary391 : TopFiberBoundary 0x1004800800000007e00c401801c0010000004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004800800000007e00c401801c0010000004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete391 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert391).beta ∈
      (AffineBoundaryCached.cert391).seeds.map Prod.fst := by
    rw [census391]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert391) 180 512
    6 AffineBoundaryCached.sheets391 AffineBoundaryCached.shadows391
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt391
    (AffineBoundaryCached.checked391) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census392 : (AffineBoundaryCached.cert392).seeds.map Prod.fst = AffineSearchData.allowed392 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 392 is a boundary. -/
theorem boundary392 : TopFiberBoundary 0x10048008000024002c0280100018010000004028003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10048008000024002c0280100018010000004028003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete392 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert392).beta ∈
      (AffineBoundaryCached.cert392).seeds.map Prod.fst := by
    rw [census392]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert392) 180 512
    8 AffineBoundaryCached.sheets392 AffineBoundaryCached.shadows392
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt392
    (AffineBoundaryCached.checked392) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census393 : (AffineBoundaryCached.cert393).seeds.map Prod.fst = AffineSearchData.allowed393 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 393 is a boundary. -/
theorem boundary393 : TopFiberBoundary 0x10048008000024032004401000c0010000004028018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10048008000024032004401000c0010000004028018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete393 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert393).beta ∈
      (AffineBoundaryCached.cert393).seeds.map Prod.fst := by
    rw [census393]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert393) 180 512
    8 AffineBoundaryCached.sheets393 AffineBoundaryCached.shadows393
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt393
    (AffineBoundaryCached.checked393) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census394 : (AffineBoundaryCached.cert394).seeds.map Prod.fst = AffineSearchData.allowed394 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 394 is a boundary. -/
theorem boundary394 : TopFiberBoundary 0x1004800800003601400040140040010000004018030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004800800003601400040140040010000004018030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete394 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert394).beta ∈
      (AffineBoundaryCached.cert394).seeds.map Prod.fst := by
    rw [census394]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert394) 180 512
    8 AffineBoundaryCached.sheets394 AffineBoundaryCached.shadows394
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt394
    (AffineBoundaryCached.checked394) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census395 : (AffineBoundaryCached.cert395).seeds.map Prod.fst = AffineSearchData.allowed395 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 395 is a boundary. -/
theorem boundary395 : TopFiberBoundary 0x1004800800007e01c00040040040010000004000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1004800800007e01c00040040040010000004000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete395 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert395).beta ∈
      (AffineBoundaryCached.cert395).seeds.map Prod.fst := by
    rw [census395]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert395) 180 512
    2 AffineBoundaryCached.sheets395 AffineBoundaryCached.shadows395
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt395
    (AffineBoundaryCached.checked395) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census396 : (AffineBoundaryCached.cert396).seeds.map Prod.fst = AffineSearchData.allowed396 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 396 is a boundary. -/
theorem boundary396 : TopFiberBoundary 0x1005000000000001205100ac0100160028000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1005000000000001205100ac0100160028000000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete396 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert396).beta ∈
      (AffineBoundaryCached.cert396).seeds.map Prod.fst := by
    rw [census396]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert396) 180 512
    4 AffineBoundaryCached.sheets396 AffineBoundaryCached.shadows396
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt396
    (AffineBoundaryCached.checked396) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census397 : (AffineBoundaryCached.cert397).seeds.map Prod.fst = AffineSearchData.allowed397 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 397 is a boundary. -/
theorem boundary397 : TopFiberBoundary 0x1006400400000001204140740080100020002000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1006400400000001204140740080100020002000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete397 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert397).beta ∈
      (AffineBoundaryCached.cert397).seeds.map Prod.fst := by
    rw [census397]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert397) 180 512
    4 AffineBoundaryCached.sheets397 AffineBoundaryCached.shadows397
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt397
    (AffineBoundaryCached.checked397) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census398 : (AffineBoundaryCached.cert398).seeds.map Prod.fst = AffineSearchData.allowed398 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 398 is a boundary. -/
theorem boundary398 : TopFiberBoundary 0x1009001000007e00e00240040000188000008000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1009001000007e00e00240040000188000008000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete398 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert398).beta ∈
      (AffineBoundaryCached.cert398).seeds.map Prod.fst := by
    rw [census398]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert398) 180 512
    8 AffineBoundaryCached.sheets398 AffineBoundaryCached.shadows398
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt398
    (AffineBoundaryCached.checked398) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census399 : (AffineBoundaryCached.cert399).seeds.map Prod.fst = AffineSearchData.allowed399 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 399 is a boundary. -/
theorem boundary399 : TopFiberBoundary 0x100a0010000000000032807400c0150018008000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x100a0010000000000032807400c0150018008000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete399 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert399).beta ∈
      (AffineBoundaryCached.cert399).seeds.map Prod.fst := by
    rw [census399]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert399) 180 512
    4 AffineBoundaryCached.sheets399 AffineBoundaryCached.shadows399
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt399
    (AffineBoundaryCached.checked399) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census400 : (AffineBoundaryCached.cert400).seeds.map Prod.fst = AffineSearchData.allowed400 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 400 is a boundary. -/
theorem boundary400 : TopFiberBoundary 0x1012002000007e00e00240040000148000010000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1012002000007e00e00240040000148000010000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete400 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert400).beta ∈
      (AffineBoundaryCached.cert400).seeds.map Prod.fst := by
    rw [census400]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert400) 180 512
    8 AffineBoundaryCached.sheets400 AffineBoundaryCached.shadows400
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt400
    (AffineBoundaryCached.checked400) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census401 : (AffineBoundaryCached.cert401).seeds.map Prod.fst = AffineSearchData.allowed401 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 401 is a boundary. -/
theorem boundary401 : TopFiberBoundary 0x1021004000000000005300ac01401a0028020000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1021004000000000005300ac01401a0028020000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete401 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert401).beta ∈
      (AffineBoundaryCached.cert401).seeds.map Prod.fst := by
    rw [census401]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert401) 180 512
    4 AffineBoundaryCached.sheets401 AffineBoundaryCached.shadows401
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt401
    (AffineBoundaryCached.checked401) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census402 : (AffineBoundaryCached.cert402).seeds.map Prod.fst = AffineSearchData.allowed402 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 402 is a boundary. -/
theorem boundary402 : TopFiberBoundary 0x1024004000007e00e002400400000c8000020000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1024004000007e00e002400400000c8000020000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete402 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert402).beta ∈
      (AffineBoundaryCached.cert402).seeds.map Prod.fst := by
    rw [census402]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert402) 180 512
    8 AffineBoundaryCached.sheets402 AffineBoundaryCached.shadows402
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt402
    (AffineBoundaryCached.checked402) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census403 : (AffineBoundaryCached.cert403).seeds.map Prod.fst = AffineSearchData.allowed403 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 403 is a boundary. -/
theorem boundary403 : TopFiberBoundary 0x103b80780000000000024018000001000003c000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x103b80780000000000024018000001000003c000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete403 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert403).beta ∈
      (AffineBoundaryCached.cert403).seeds.map Prod.fst := by
    rw [census403]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert403) 180 512
    6 AffineBoundaryCached.sheets403 AffineBoundaryCached.shadows403
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt403
    (AffineBoundaryCached.checked403) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty

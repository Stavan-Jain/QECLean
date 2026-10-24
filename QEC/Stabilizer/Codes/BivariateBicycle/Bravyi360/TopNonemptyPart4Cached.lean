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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart4
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census404 : (AffineBoundaryCached.cert404).seeds.map Prod.fst = AffineSearchData.allowed404 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 404 is a boundary. -/
theorem boundary404 : TopFiberBoundary 0x103d40740000000000024018000002000003a000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x103d40740000000000024018000002000003a000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete404 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert404).beta ∈
      (AffineBoundaryCached.cert404).seeds.map Prod.fst := by
    rw [census404]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert404) 180 512
    6 AffineBoundaryCached.sheets404 AffineBoundaryCached.shadows404
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt404
    (AffineBoundaryCached.checked404) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census405 : (AffineBoundaryCached.cert405).seeds.map Prod.fst = AffineSearchData.allowed405 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 405 is a boundary. -/
theorem boundary405 : TopFiberBoundary 0x1040000040000000fc01c000000e006001200200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1040000040000000fc01c000000e006001200200000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete405 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert405).beta ∈
      (AffineBoundaryCached.cert405).seeds.map Prod.fst := by
    rw [census405]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert405) 180 512
    4 AffineBoundaryCached.sheets405 AffineBoundaryCached.shadows405
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt405
    (AffineBoundaryCached.checked405) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census406 : (AffineBoundaryCached.cert406).seeds.map Prod.fst = AffineSearchData.allowed406 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 406 is a boundary. -/
theorem boundary406 : TopFiberBoundary 0x1040000828008020000004000036006002800400940 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1040000828008020000004000036006002800400940)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete406 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert406).beta ∈
      (AffineBoundaryCached.cert406).seeds.map Prod.fst := by
    rw [census406]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert406) 180 512
    4 AffineBoundaryCached.sheets406 AffineBoundaryCached.shadows406
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt406
    (AffineBoundaryCached.checked406) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census407 : (AffineBoundaryCached.cert407).seeds.map Prod.fst = AffineSearchData.allowed407 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 407 is a boundary. -/
theorem boundary407 : TopFiberBoundary 0x10403b80380000000000000000360000012001c0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10403b80380000000000000000360000012001c0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete407 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert407).beta ∈
      (AffineBoundaryCached.cert407).seeds.map Prod.fst := by
    rw [census407]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert407) 180 512
    6 AffineBoundaryCached.sheets407 AffineBoundaryCached.shadows407
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt407
    (AffineBoundaryCached.checked407) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census408 : (AffineBoundaryCached.cert408).seeds.map Prod.fst = AffineSearchData.allowed408 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 408 is a boundary. -/
theorem boundary408 : TopFiberBoundary 0x1048008000007e00e00240040000c08000040000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1048008000007e00e00240040000c08000040000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete408 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert408).beta ∈
      (AffineBoundaryCached.cert408).seeds.map Prod.fst := by
    rw [census408]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert408) 180 512
    8 AffineBoundaryCached.sheets408 AffineBoundaryCached.shadows408
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt408
    (AffineBoundaryCached.checked408) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census409 : (AffineBoundaryCached.cert409).seeds.map Prod.fst = AffineSearchData.allowed409 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 409 is a boundary. -/
theorem boundary409 : TopFiberBoundary 0x1090010000007e00e00240040000a08000080000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1090010000007e00e00240040000a08000080000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete409 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert409).beta ∈
      (AffineBoundaryCached.cert409).seeds.map Prod.fst := by
    rw [census409]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert409) 180 512
    8 AffineBoundaryCached.sheets409 AffineBoundaryCached.shadows409
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt409
    (AffineBoundaryCached.checked409) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census410 : (AffineBoundaryCached.cert410).seeds.map Prod.fst = AffineSearchData.allowed410 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 410 is a boundary. -/
theorem boundary410 : TopFiberBoundary 0x10c00800400000000900a8028031004001600200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10c00800400000000900a8028031004001600200000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete410 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert410).beta ∈
      (AffineBoundaryCached.cert410).seeds.map Prod.fst := by
    rw [census410]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert410) 180 512
    4 AffineBoundaryCached.sheets410 AffineBoundaryCached.shadows410
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt410
    (AffineBoundaryCached.checked410) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census411 : (AffineBoundaryCached.cert411).seeds.map Prod.fst = AffineSearchData.allowed411 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 411 is a boundary. -/
theorem boundary411 : TopFiberBoundary 0x10c02c00000000000900a8028031002001600000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10c02c00000000000900a8028031002001600000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete411 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert411).beta ∈
      (AffineBoundaryCached.cert411).seeds.map Prod.fst := by
    rw [census411]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert411) 180 512
    8 AffineBoundaryCached.sheets411 AffineBoundaryCached.shadows411
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt411
    (AffineBoundaryCached.checked411) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census412 : (AffineBoundaryCached.cert412).seeds.map Prod.fst = AffineSearchData.allowed412 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 412 is a boundary. -/
theorem boundary412 : TopFiberBoundary 0x1100900000000000240b00140013028004800000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1100900000000000240b00140013028004800000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete412 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert412).beta ∈
      (AffineBoundaryCached.cert412).seeds.map Prod.fst := by
    rw [census412]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert412) 180 512
    8 AffineBoundaryCached.sheets412 AffineBoundaryCached.shadows412
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt412
    (AffineBoundaryCached.checked412) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census413 : (AffineBoundaryCached.cert413).seeds.map Prod.fst = AffineSearchData.allowed413 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 413 is a boundary. -/
theorem boundary413 : TopFiberBoundary 0x1104100800000000000b4014001b030004804000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1104100800000000000b4014001b030004804000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete413 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert413).beta ∈
      (AffineBoundaryCached.cert413).seeds.map Prod.fst := by
    rw [census413]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert413) 180 512
    8 AffineBoundaryCached.sheets413 AffineBoundaryCached.shadows413
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt413
    (AffineBoundaryCached.checked413) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census414 : (AffineBoundaryCached.cert414).seeds.map Prod.fst = AffineSearchData.allowed414 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 414 is a boundary. -/
theorem boundary414 : TopFiberBoundary 0x1120020000007e00e00240040000608000100000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1120020000007e00e00240040000608000100000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete414 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert414).beta ∈
      (AffineBoundaryCached.cert414).seeds.map Prod.fst := by
    rw [census414]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert414) 180 512
    8 AffineBoundaryCached.sheets414 AffineBoundaryCached.shadows414
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt414
    (AffineBoundaryCached.checked414) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census415 : (AffineBoundaryCached.cert415).seeds.map Prod.fst = AffineSearchData.allowed415 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 415 is a boundary. -/
theorem boundary415 : TopFiberBoundary 0x1200040828008020000004000030006002a00400940 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200040828008020000004000030006002a00400940)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete415 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert415).beta ∈
      (AffineBoundaryCached.cert415).seeds.map Prod.fst := by
    rw [census415]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert415) 180 512
    4 AffineBoundaryCached.sheets415 AffineBoundaryCached.shadows415
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt415
    (AffineBoundaryCached.checked415) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census416 : (AffineBoundaryCached.cert416).seeds.map Prod.fst = AffineSearchData.allowed416 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 416 is a boundary. -/
theorem boundary416 : TopFiberBoundary 0x12002000000000039c07c00000c8000001000000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000000039c07c00000c8000001000000018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete416 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert416).beta ∈
      (AffineBoundaryCached.cert416).seeds.map Prod.fst := by
    rw [census416]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert416) 180 512
    2 AffineBoundaryCached.sheets416 AffineBoundaryCached.shadows416
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt416
    (AffineBoundaryCached.checked416) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census417 : (AffineBoundaryCached.cert417).seeds.map Prod.fst = AffineSearchData.allowed417 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 417 is a boundary. -/
theorem boundary417 : TopFiberBoundary 0x12002000000000055c0bc0000148000001000000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000000055c0bc0000148000001000000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete417 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert417).beta ∈
      (AffineBoundaryCached.cert417).seeds.map Prod.fst := by
    rw [census417]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert417) 180 512
    2 AffineBoundaryCached.sheets417 AffineBoundaryCached.shadows417
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt417
    (AffineBoundaryCached.checked417) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census418 : (AffineBoundaryCached.cert418).seeds.map Prod.fst = AffineSearchData.allowed418 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 418 is a boundary. -/
theorem boundary418 : TopFiberBoundary 0x12002000000000063c0dc0000188000001000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000000063c0dc0000188000001000000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete418 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert418).beta ∈
      (AffineBoundaryCached.cert418).seeds.map Prod.fst := by
    rw [census418]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert418) 180 512
    4 AffineBoundaryCached.sheets418 AffineBoundaryCached.shadows418
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt418
    (AffineBoundaryCached.checked418) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census419 : (AffineBoundaryCached.cert419).seeds.map Prod.fst = AffineSearchData.allowed419 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 419 is a boundary. -/
theorem boundary419 : TopFiberBoundary 0x1200200000000007380f800001c0000001000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000007380f800001c0000001000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete419 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert419).beta ∈
      (AffineBoundaryCached.cert419).seeds.map Prod.fst := by
    rw [census419]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert419) 180 512
    4 AffineBoundaryCached.sheets419 AffineBoundaryCached.shadows419
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt419
    (AffineBoundaryCached.checked419) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census420 : (AffineBoundaryCached.cert420).seeds.map Prod.fst = AffineSearchData.allowed420 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 420 is a boundary. -/
theorem boundary420 : TopFiberBoundary 0x1200200000000007700f000001d0000001000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000007700f000001d0000001000000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete420 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert420).beta ∈
      (AffineBoundaryCached.cert420).seeds.map Prod.fst := by
    rw [census420]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert420) 180 512
    6 AffineBoundaryCached.sheets420 AffineBoundaryCached.shadows420
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt420
    (AffineBoundaryCached.checked420) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census421 : (AffineBoundaryCached.cert421).seeds.map Prod.fst = AffineSearchData.allowed421 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 421 is a boundary. -/
theorem boundary421 : TopFiberBoundary 0x1200200000000007a80e800001e0000001000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000007a80e800001e0000001000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete421 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert421).beta ∈
      (AffineBoundaryCached.cert421).seeds.map Prod.fst := by
    rw [census421]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert421) 180 512
    6 AffineBoundaryCached.sheets421 AffineBoundaryCached.shadows421
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt421
    (AffineBoundaryCached.checked421) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census422 : (AffineBoundaryCached.cert422).seeds.map Prod.fst = AffineSearchData.allowed422 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 422 is a boundary. -/
theorem boundary422 : TopFiberBoundary 0x1200200000000009fc11c0000208000001000000180 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000009fc11c0000208000001000000180)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete422 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert422).beta ∈
      (AffineBoundaryCached.cert422).seeds.map Prod.fst := by
    rw [census422]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert422) 180 512
    8 AffineBoundaryCached.sheets422 AffineBoundaryCached.shadows422
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt422
    (AffineBoundaryCached.checked422) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census423 : (AffineBoundaryCached.cert423).seeds.map Prod.fst = AffineSearchData.allowed423 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 423 is a boundary. -/
theorem boundary423 : TopFiberBoundary 0x1200200000000012fc21c0000408000001000000140 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000012fc21c0000408000001000000140)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete423 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert423).beta ∈
      (AffineBoundaryCached.cert423).seeds.map Prod.fst := by
    rw [census423]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert423) 180 512
    8 AffineBoundaryCached.sheets423 AffineBoundaryCached.shadows423
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt423
    (AffineBoundaryCached.checked423) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census424 : (AffineBoundaryCached.cert424).seeds.map Prod.fst = AffineSearchData.allowed424 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 424 is a boundary. -/
theorem boundary424 : TopFiberBoundary 0x1200200000000024fc41c00008080000010000000c0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000024fc41c00008080000010000000c0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete424 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert424).beta ∈
      (AffineBoundaryCached.cert424).seeds.map Prod.fst := by
    rw [census424]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert424) 180 512
    8 AffineBoundaryCached.sheets424 AffineBoundaryCached.shadows424
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt424
    (AffineBoundaryCached.checked424) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census425 : (AffineBoundaryCached.cert425).seeds.map Prod.fst = AffineSearchData.allowed425 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 425 is a boundary. -/
theorem boundary425 : TopFiberBoundary 0x1200200000000048fc81c0001008000001000000c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000048fc81c0001008000001000000c00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete425 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert425).beta ∈
      (AffineBoundaryCached.cert425).seeds.map Prod.fst := by
    rw [census425]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert425) 180 512
    8 AffineBoundaryCached.sheets425 AffineBoundaryCached.shadows425
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt425
    (AffineBoundaryCached.checked425) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census426 : (AffineBoundaryCached.cert426).seeds.map Prod.fst = AffineSearchData.allowed426 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 426 is a boundary. -/
theorem boundary426 : TopFiberBoundary 0x1200200000000090fd01c0002008000001000000a00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000090fd01c0002008000001000000a00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete426 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert426).beta ∈
      (AffineBoundaryCached.cert426).seeds.map Prod.fst := by
    rw [census426]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert426) 180 512
    8 AffineBoundaryCached.sheets426 AffineBoundaryCached.shadows426
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt426
    (AffineBoundaryCached.checked426) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census427 : (AffineBoundaryCached.cert427).seeds.map Prod.fst = AffineSearchData.allowed427 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 427 is a boundary. -/
theorem boundary427 : TopFiberBoundary 0x1200200000000120fe01c0004008000001000000600 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000120fe01c0004008000001000000600)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete427 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert427).beta ∈
      (AffineBoundaryCached.cert427).seeds.map Prod.fst := by
    rw [census427]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert427) 180 512
    8 AffineBoundaryCached.sheets427 AffineBoundaryCached.shadows427
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt427
    (AffineBoundaryCached.checked427) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census428 : (AffineBoundaryCached.cert428).seeds.map Prod.fst = AffineSearchData.allowed428 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 428 is a boundary. -/
theorem boundary428 : TopFiberBoundary 0x12002000000006c0f001c0018008000001000003000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000006c0f001c0018008000001000003000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete428 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert428).beta ∈
      (AffineBoundaryCached.cert428).seeds.map Prod.fst := by
    rw [census428]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert428) 180 512
    2 AffineBoundaryCached.sheets428 AffineBoundaryCached.shadows428
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt428
    (AffineBoundaryCached.checked428) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census429 : (AffineBoundaryCached.cert429).seeds.map Prod.fst = AffineSearchData.allowed429 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 429 is a boundary. -/
theorem boundary429 : TopFiberBoundary 0x1200200000000b40e801c0028008000001000005000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000b40e801c0028008000001000005000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete429 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert429).beta ∈
      (AffineBoundaryCached.cert429).seeds.map Prod.fst := by
    rw [census429]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert429) 180 512
    2 AffineBoundaryCached.sheets429 AffineBoundaryCached.shadows429
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt429
    (AffineBoundaryCached.checked429) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census430 : (AffineBoundaryCached.cert430).seeds.map Prod.fst = AffineSearchData.allowed430 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 430 is a boundary. -/
theorem boundary430 : TopFiberBoundary 0x1200200000000d80e401c0030008000001000006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000d80e401c0030008000001000006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete430 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert430).beta ∈
      (AffineBoundaryCached.cert430).seeds.map Prod.fst := by
    rw [census430]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert430) 180 512
    4 AffineBoundaryCached.sheets430 AffineBoundaryCached.shadows430
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt430
    (AffineBoundaryCached.checked430) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census431 : (AffineBoundaryCached.cert431).seeds.map Prod.fst = AffineSearchData.allowed431 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 431 is a boundary. -/
theorem boundary431 : TopFiberBoundary 0x1200200000000fc0c40180038000000001000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000000fc0c40180038000000001000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete431 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert431).beta ∈
      (AffineBoundaryCached.cert431).seeds.map Prod.fst := by
    rw [census431]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert431) 180 512
    4 AffineBoundaryCached.sheets431 AffineBoundaryCached.shadows431
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt431
    (AffineBoundaryCached.checked431) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census432 : (AffineBoundaryCached.cert432).seeds.map Prod.fst = AffineSearchData.allowed432 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 432 is a boundary. -/
theorem boundary432 : TopFiberBoundary 0x1200200000001040d801c0048008000001000036000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000001040d801c0048008000001000036000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete432 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert432).beta ∈
      (AffineBoundaryCached.cert432).seeds.map Prod.fst := by
    rw [census432]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert432) 180 512
    4 AffineBoundaryCached.sheets432 AffineBoundaryCached.shadows432
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt432
    (AffineBoundaryCached.checked432) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census433 : (AffineBoundaryCached.cert433).seeds.map Prod.fst = AffineSearchData.allowed433 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 433 is a boundary. -/
theorem boundary433 : TopFiberBoundary 0x1200200000002080b401c009000800000100002d000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000002080b401c009000800000100002d000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete433 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert433).beta ∈
      (AffineBoundaryCached.cert433).seeds.map Prod.fst := by
    rw [census433]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert433) 180 512
    4 AffineBoundaryCached.sheets433 AffineBoundaryCached.shadows433
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt433
    (AffineBoundaryCached.checked433) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census434 : (AffineBoundaryCached.cert434).seeds.map Prod.fst = AffineSearchData.allowed434 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 434 is a boundary. -/
theorem boundary434 : TopFiberBoundary 0x12002000000036009c01c00c0008000001000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000036009c01c00c0008000001000018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete434 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert434).beta ∈
      (AffineBoundaryCached.cert434).seeds.map Prod.fst := by
    rw [census434]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert434) 180 512
    2 AffineBoundaryCached.sheets434 AffineBoundaryCached.shadows434
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt434
    (AffineBoundaryCached.checked434) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census435 : (AffineBoundaryCached.cert435).seeds.map Prod.fst = AffineSearchData.allowed435 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 435 is a boundary. -/
theorem boundary435 : TopFiberBoundary 0x12002000000041006c01c012000800000100001b000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x12002000000041006c01c012000800000100001b000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete435 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert435).beta ∈
      (AffineBoundaryCached.cert435).seeds.map Prod.fst := by
    rw [census435]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert435) 180 512
    4 AffineBoundaryCached.sheets435 AffineBoundaryCached.shadows435
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt435
    (AffineBoundaryCached.checked435) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census436 : (AffineBoundaryCached.cert436).seeds.map Prod.fst = AffineSearchData.allowed436 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 436 is a boundary. -/
theorem boundary436 : TopFiberBoundary 0x1200200000005a005c01c0140008000001000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000005a005c01c0140008000001000028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete436 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert436).beta ∈
      (AffineBoundaryCached.cert436).seeds.map Prod.fst := by
    rw [census436]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert436) 180 512
    2 AffineBoundaryCached.sheets436 AffineBoundaryCached.shadows436
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt436
    (AffineBoundaryCached.checked436) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census437 : (AffineBoundaryCached.cert437).seeds.map Prod.fst = AffineSearchData.allowed437 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 437 is a boundary. -/
theorem boundary437 : TopFiberBoundary 0x1200200000006c003c01c0180008000001000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000006c003c01c0180008000001000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete437 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert437).beta ∈
      (AffineBoundaryCached.cert437).seeds.map Prod.fst := by
    rw [census437]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert437) 180 512
    4 AffineBoundaryCached.sheets437 AffineBoundaryCached.shadows437
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt437
    (AffineBoundaryCached.checked437) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census438 : (AffineBoundaryCached.cert438).seeds.map Prod.fst = AffineSearchData.allowed438 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 438 is a boundary. -/
theorem boundary438 : TopFiberBoundary 0x1200200000007e003801801c0000000001000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200000007e003801801c0000000001000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete438 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert438).beta ∈
      (AffineBoundaryCached.cert438).seeds.map Prod.fst := by
    rw [census438]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert438) 180 512
    4 AffineBoundaryCached.sheets438 AffineBoundaryCached.shadows438
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt438
    (AffineBoundaryCached.checked438) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census439 : (AffineBoundaryCached.cert439).seeds.map Prod.fst = AffineSearchData.allowed439 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 439 is a boundary. -/
theorem boundary439 : TopFiberBoundary 0x1200200048008000fc01c0000008000001c00000040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200200048008000fc01c0000008000001c00000040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete439 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert439).beta ∈
      (AffineBoundaryCached.cert439).seeds.map Prod.fst := by
    rw [census439]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert439) 180 512
    8 AffineBoundaryCached.sheets439 AffineBoundaryCached.shadows439
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt439
    (AffineBoundaryCached.checked439) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census440 : (AffineBoundaryCached.cert440).seeds.map Prod.fst = AffineSearchData.allowed440 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 440 is a boundary. -/
theorem boundary440 : TopFiberBoundary 0x1200290010000000fc01c0000008000a01000080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200290010000000fc01c0000008000a01000080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete440 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert440).beta ∈
      (AffineBoundaryCached.cert440).seeds.map Prod.fst := by
    rw [census440]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert440) 180 512
    8 AffineBoundaryCached.sheets440 AffineBoundaryCached.shadows440
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt440
    (AffineBoundaryCached.checked440) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census441 : (AffineBoundaryCached.cert441).seeds.map Prod.fst = AffineSearchData.allowed441 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 441 is a boundary. -/
theorem boundary441 : TopFiberBoundary 0x1200320020000000fc01c0000008000601000100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200320020000000fc01c0000008000601000100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete441 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert441).beta ∈
      (AffineBoundaryCached.cert441).seeds.map Prod.fst := by
    rw [census441]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert441) 180 512
    8 AffineBoundaryCached.sheets441 AffineBoundaryCached.shadows441
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt441
    (AffineBoundaryCached.checked441) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census442 : (AffineBoundaryCached.cert442).seeds.map Prod.fst = AffineSearchData.allowed442 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 442 is a boundary. -/
theorem boundary442 : TopFiberBoundary 0x1200680080000000fc01c0000008005001000400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200680080000000fc01c0000008005001000400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete442 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert442).beta ∈
      (AffineBoundaryCached.cert442).seeds.map Prod.fst := by
    rw [census442]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert442) 180 512
    8 AffineBoundaryCached.sheets442 AffineBoundaryCached.shadows442
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt442
    (AffineBoundaryCached.checked442) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census443 : (AffineBoundaryCached.cert443).seeds.map Prod.fst = AffineSearchData.allowed443 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 443 is a boundary. -/
theorem boundary443 : TopFiberBoundary 0x1200b00100000000fc01c0000008003001000800000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200b00100000000fc01c0000008003001000800000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete443 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert443).beta ∈
      (AffineBoundaryCached.cert443).seeds.map Prod.fst := by
    rw [census443]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert443) 180 512
    8 AffineBoundaryCached.sheets443 AffineBoundaryCached.shadows443
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt443
    (AffineBoundaryCached.checked443) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census444 : (AffineBoundaryCached.cert444).seeds.map Prod.fst = AffineSearchData.allowed444 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 444 is a boundary. -/
theorem boundary444 : TopFiberBoundary 0x1200ce01e0000000000000000030000601000f00000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200ce01e0000000000000000030000601000f00000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete444 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert444).beta ∈
      (AffineBoundaryCached.cert444).seeds.map Prod.fst := by
    rw [census444]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert444) 180 512
    6 AffineBoundaryCached.sheets444 AffineBoundaryCached.shadows444
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt444
    (AffineBoundaryCached.checked444) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census445 : (AffineBoundaryCached.cert445).seeds.map Prod.fst = AffineSearchData.allowed445 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 445 is a boundary. -/
theorem boundary445 : TopFiberBoundary 0x1200d501d0000000000000000030000a01000e80000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200d501d0000000000000000030000a01000e80000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete445 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert445).beta ∈
      (AffineBoundaryCached.cert445).seeds.map Prod.fst := by
    rw [census445]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert445) 180 512
    6 AffineBoundaryCached.sheets445 AffineBoundaryCached.shadows445
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt445
    (AffineBoundaryCached.checked445) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census446 : (AffineBoundaryCached.cert446).seeds.map Prod.fst = AffineSearchData.allowed446 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 446 is a boundary. -/
theorem boundary446 : TopFiberBoundary 0x1200d881c8000000000000000030000c01000e40000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200d881c8000000000000000030000c01000e40000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete446 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert446).beta ∈
      (AffineBoundaryCached.cert446).seeds.map Prod.fst := by
    rw [census446]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert446) 180 512
    6 AffineBoundaryCached.sheets446 AffineBoundaryCached.shadows446
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt446
    (AffineBoundaryCached.checked446) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census447 : (AffineBoundaryCached.cert447).seeds.map Prod.fst = AffineSearchData.allowed447 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 447 is a boundary. -/
theorem boundary447 : TopFiberBoundary 0x1200dc0188008000000000000030000001c00e00040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200dc0188008000000000000030000001c00e00040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete447 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert447).beta ∈
      (AffineBoundaryCached.cert447).seeds.map Prod.fst := by
    rw [census447]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert447) 180 512
    6 AffineBoundaryCached.sheets447 AffineBoundaryCached.shadows447
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt447
    (AffineBoundaryCached.checked447) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census448 : (AffineBoundaryCached.cert448).seeds.map Prod.fst = AffineSearchData.allowed448 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 448 is a boundary. -/
theorem boundary448 : TopFiberBoundary 0x1200dc01c0000000480080000020000001000e00005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200dc01c0000000480080000020000001000e00005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete448 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert448).beta ∈
      (AffineBoundaryCached.cert448).seeds.map Prod.fst := by
    rw [census448]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert448) 180 512
    6 AffineBoundaryCached.sheets448 AffineBoundaryCached.shadows448
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt448
    (AffineBoundaryCached.checked448) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census449 : (AffineBoundaryCached.cert449).seeds.map Prod.fst = AffineSearchData.allowed449 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 449 is a boundary. -/
theorem boundary449 : TopFiberBoundary 0x1200dc01c0000000900100000010000001000e00003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1200dc01c0000000900100000010000001000e00003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete449 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert449).beta ∈
      (AffineBoundaryCached.cert449).seeds.map Prod.fst := by
    rw [census449]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert449) 180 512
    6 AffineBoundaryCached.sheets449 AffineBoundaryCached.shadows449
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt449
    (AffineBoundaryCached.checked449) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census450 : (AffineBoundaryCached.cert450).seeds.map Prod.fst = AffineSearchData.allowed450 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 450 is a boundary. -/
theorem boundary450 : TopFiberBoundary 0x1202600400000000fc01c0000008028001002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1202600400000000fc01c0000008028001002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete450 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert450).beta ∈
      (AffineBoundaryCached.cert450).seeds.map Prod.fst := by
    rw [census450]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert450) 180 512
    8 AffineBoundaryCached.sheets450 AffineBoundaryCached.shadows450
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt450
    (AffineBoundaryCached.checked450) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census451 : (AffineBoundaryCached.cert451).seeds.map Prod.fst = AffineSearchData.allowed451 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 451 is a boundary. -/
theorem boundary451 : TopFiberBoundary 0x1204a00800000000fc01c0000008018001004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1204a00800000000fc01c0000008018001004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete451 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert451).beta ∈
      (AffineBoundaryCached.cert451).seeds.map Prod.fst := by
    rw [census451]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert451) 180 512
    8 AffineBoundaryCached.sheets451 AffineBoundaryCached.shadows451
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt451
    (AffineBoundaryCached.checked451) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census452 : (AffineBoundaryCached.cert452).seeds.map Prod.fst = AffineSearchData.allowed452 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 452 is a boundary. -/
theorem boundary452 : TopFiberBoundary 0x1207c00e00000000480080000020000001007000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1207c00e00000000480080000020000001007000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete452 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert452).beta ∈
      (AffineBoundaryCached.cert452).seeds.map Prod.fst := by
    rw [census452]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert452) 180 512
    6 AffineBoundaryCached.sheets452 AffineBoundaryCached.shadows452
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt452
    (AffineBoundaryCached.checked452) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census453 : (AffineBoundaryCached.cert453).seeds.map Prod.fst = AffineSearchData.allowed453 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 453 is a boundary. -/
theorem boundary453 : TopFiberBoundary 0x1207c00e00000000900100000010000001007000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1207c00e00000000900100000010000001007000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete453 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert453).beta ∈
      (AffineBoundaryCached.cert453).seeds.map Prod.fst := by
    rw [census453]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert453) 180 512
    6 AffineBoundaryCached.sheets453 AffineBoundaryCached.shadows453
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt453
    (AffineBoundaryCached.checked453) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census454 : (AffineBoundaryCached.cert454).seeds.map Prod.fst = AffineSearchData.allowed454 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 454 is a boundary. -/
theorem boundary454 : TopFiberBoundary 0x1209201000000000fc01c0000008180001008000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1209201000000000fc01c0000008180001008000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete454 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert454).beta ∈
      (AffineBoundaryCached.cert454).seeds.map Prod.fst := by
    rw [census454]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert454) 180 512
    8 AffineBoundaryCached.sheets454 AffineBoundaryCached.shadows454
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt454
    (AffineBoundaryCached.checked454) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census455 : (AffineBoundaryCached.cert455).seeds.map Prod.fst = AffineSearchData.allowed455 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 455 is a boundary. -/
theorem boundary455 : TopFiberBoundary 0x1212202000000000fc01c0000008140001010000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1212202000000000fc01c0000008140001010000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete455 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert455).beta ∈
      (AffineBoundaryCached.cert455).seeds.map Prod.fst := by
    rw [census455]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert455) 180 512
    8 AffineBoundaryCached.sheets455 AffineBoundaryCached.shadows455
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt455
    (AffineBoundaryCached.checked455) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census456 : (AffineBoundaryCached.cert456).seeds.map Prod.fst = AffineSearchData.allowed456 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 456 is a boundary. -/
theorem boundary456 : TopFiberBoundary 0x1224204000000000fc01c00000080c0001020000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1224204000000000fc01c00000080c0001020000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete456 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert456).beta ∈
      (AffineBoundaryCached.cert456).seeds.map Prod.fst := by
    rw [census456]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert456) 180 512
    8 AffineBoundaryCached.sheets456 AffineBoundaryCached.shadows456
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt456
    (AffineBoundaryCached.checked456) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census457 : (AffineBoundaryCached.cert457).seeds.map Prod.fst = AffineSearchData.allowed457 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 457 is a boundary. -/
theorem boundary457 : TopFiberBoundary 0x1248208000000000fc01c0000008c00001040000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1248208000000000fc01c0000008c00001040000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete457 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert457).beta ∈
      (AffineBoundaryCached.cert457).seeds.map Prod.fst := by
    rw [census457]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert457) 180 512
    8 AffineBoundaryCached.sheets457 AffineBoundaryCached.shadows457
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt457
    (AffineBoundaryCached.checked457) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census458 : (AffineBoundaryCached.cert458).seeds.map Prod.fst = AffineSearchData.allowed458 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 458 is a boundary. -/
theorem boundary458 : TopFiberBoundary 0x128148020000000000048014001d020003401000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x128148020000000000048014001d020003401000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete458 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert458).beta ∈
      (AffineBoundaryCached.cert458).seeds.map Prod.fst := by
    rw [census458]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert458) 180 512
    8 AffineBoundaryCached.sheets458 AffineBoundaryCached.shadows458
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt458
    (AffineBoundaryCached.checked458) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census459 : (AffineBoundaryCached.cert459).seeds.map Prod.fst = AffineSearchData.allowed459 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 459 is a boundary. -/
theorem boundary459 : TopFiberBoundary 0x1290210000000000fc01c0000008a00001080000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1290210000000000fc01c0000008a00001080000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete459 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert459).beta ∈
      (AffineBoundaryCached.cert459).seeds.map Prod.fst := by
    rw [census459]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert459) 180 512
    8 AffineBoundaryCached.sheets459 AffineBoundaryCached.shadows459
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt459
    (AffineBoundaryCached.checked459) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census460 : (AffineBoundaryCached.cert460).seeds.map Prod.fst = AffineSearchData.allowed460 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 460 is a boundary. -/
theorem boundary460 : TopFiberBoundary 0x1320220000000000fc01c0000008600001100000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1320220000000000fc01c0000008600001100000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete460 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert460).beta ∈
      (AffineBoundaryCached.cert460).seeds.map Prod.fst := by
    rw [census460]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert460) 180 512
    8 AffineBoundaryCached.sheets460 AffineBoundaryCached.shadows460
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt460
    (AffineBoundaryCached.checked460) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census461 : (AffineBoundaryCached.cert461).seeds.map Prod.fst = AffineSearchData.allowed461 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 461 is a boundary. -/
theorem boundary461 : TopFiberBoundary 0x1400200000000000458058018023003001000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400200000000000458058018023003001000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete461 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert461).beta ∈
      (AffineBoundaryCached.cert461).seeds.map Prod.fst := by
    rw [census461]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert461) 180 512
    4 AffineBoundaryCached.sheets461 AffineBoundaryCached.shadows461
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt461
    (AffineBoundaryCached.checked461) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census462 : (AffineBoundaryCached.cert462).seeds.map Prod.fst = AffineSearchData.allowed462 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 462 is a boundary. -/
theorem boundary462 : TopFiberBoundary 0x1400400000000000d807400c0018018002000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400400000000000d807400c0018018002000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete462 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert462).beta ∈
      (AffineBoundaryCached.cert462).seeds.map Prod.fst := by
    rw [census462]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert462) 180 512
    8 AffineBoundaryCached.sheets462 AffineBoundaryCached.shadows462
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt462
    (AffineBoundaryCached.checked462) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census463 : (AffineBoundaryCached.cert463).seeds.map Prod.fst = AffineSearchData.allowed463 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 463 is a boundary. -/
theorem boundary463 : TopFiberBoundary 0x1400400000000001dc05000c0050018002000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400400000000001dc05000c0050018002000000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete463 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert463).beta ∈
      (AffineBoundaryCached.cert463).seeds.map Prod.fst := by
    rw [census463]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert463) 180 512
    2 AffineBoundaryCached.sheets463 AffineBoundaryCached.shadows463
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt463
    (AffineBoundaryCached.checked463) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census464 : (AffineBoundaryCached.cert464).seeds.map Prod.fst = AffineSearchData.allowed464 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 464 is a boundary. -/
theorem boundary464 : TopFiberBoundary 0x1400400000001200dc0700080010018002000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400400000001200dc0700080010018002000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete464 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert464).beta ∈
      (AffineBoundaryCached.cert464).seeds.map Prod.fst := by
    rw [census464]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert464) 180 512
    2 AffineBoundaryCached.sheets464 AffineBoundaryCached.shadows464
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt464
    (AffineBoundaryCached.checked464) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census465 : (AffineBoundaryCached.cert465).seeds.map Prod.fst = AffineSearchData.allowed465 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 465 is a boundary. -/
theorem boundary465 : TopFiberBoundary 0x1400400000002400080640040038018002000028005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400400000002400080640040038018002000028005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete465 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert465).beta ∈
      (AffineBoundaryCached.cert465).seeds.map Prod.fst := by
    rw [census465]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert465) 180 512
    8 AffineBoundaryCached.sheets465 AffineBoundaryCached.shadows465
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt465
    (AffineBoundaryCached.checked465) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census466 : (AffineBoundaryCached.cert466).seeds.map Prod.fst = AffineSearchData.allowed466 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 466 is a boundary. -/
theorem boundary466 : TopFiberBoundary 0x1400400000003600440680000020018002000018006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1400400000003600440680000020018002000018006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete466 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert466).beta ∈
      (AffineBoundaryCached.cert466).seeds.map Prod.fst := by
    rw [census466]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert466) 180 512
    4 AffineBoundaryCached.sheets466 AffineBoundaryCached.shadows466
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt466
    (AffineBoundaryCached.checked466) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census467 : (AffineBoundaryCached.cert467).seeds.map Prod.fst = AffineSearchData.allowed467 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 467 is a boundary. -/
theorem boundary467 : TopFiberBoundary 0x14004000000036006006c0000028018002000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x14004000000036006006c0000028018002000018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete467 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert467).beta ∈
      (AffineBoundaryCached.cert467).seeds.map Prod.fst := by
    rw [census467]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert467) 180 512
    8 AffineBoundaryCached.sheets467 AffineBoundaryCached.shadows467
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt467
    (AffineBoundaryCached.checked467) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census468 : (AffineBoundaryCached.cert468).seeds.map Prod.fst = AffineSearchData.allowed468 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 468 is a boundary. -/
theorem boundary468 : TopFiberBoundary 0x1402000400000000fc07000c0010030002002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1402000400000000fc07000c0010030002002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete468 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert468).beta ∈
      (AffineBoundaryCached.cert468).seeds.map Prod.fst := by
    rw [census468]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert468) 180 512
    2 AffineBoundaryCached.sheets468 AffineBoundaryCached.shadows468
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt468
    (AffineBoundaryCached.checked468) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census469 : (AffineBoundaryCached.cert469).seeds.map Prod.fst = AffineSearchData.allowed469 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 469 is a boundary. -/
theorem boundary469 : TopFiberBoundary 0x14032006000000002406800c0020000002003000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x14032006000000002406800c0020000002003000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete469 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert469).beta ∈
      (AffineBoundaryCached.cert469).seeds.map Prod.fst := by
    rw [census469]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert469) 180 512
    4 AffineBoundaryCached.sheets469 AffineBoundaryCached.shadows469
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt469
    (AffineBoundaryCached.checked469) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census470 : (AffineBoundaryCached.cert470).seeds.map Prod.fst = AffineSearchData.allowed470 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 470 is a boundary. -/
theorem boundary470 : TopFiberBoundary 0x1404c00800000000fc07000c0010000002004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1404c00800000000fc07000c0010000002004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete470 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert470).beta ∈
      (AffineBoundaryCached.cert470).seeds.map Prod.fst := by
    rw [census470]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert470) 180 512
    2 AffineBoundaryCached.sheets470 AffineBoundaryCached.shadows470
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt470
    (AffineBoundaryCached.checked470) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census471 : (AffineBoundaryCached.cert471).seeds.map Prod.fst = AffineSearchData.allowed471 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 471 is a boundary. -/
theorem boundary471 : TopFiberBoundary 0x144144020000000000048014001e020003201000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x144144020000000000048014001e020003201000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete471 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert471).beta ∈
      (AffineBoundaryCached.cert471).seeds.map Prod.fst := by
    rw [census471]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert471) 180 512
    8 AffineBoundaryCached.sheets471 AffineBoundaryCached.shadows471
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt471
    (AffineBoundaryCached.checked471) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census472 : (AffineBoundaryCached.cert472).seeds.map Prod.fst = AffineSearchData.allowed472 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 472 is a boundary. -/
theorem boundary472 : TopFiberBoundary 0x1600200000000000f5016802800a002001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1600200000000000f5016802800a002001000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete472 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert472).beta ∈
      (AffineBoundaryCached.cert472).seeds.map Prod.fst := by
    rw [census472]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert472) 180 512
    4 AffineBoundaryCached.sheets472 AffineBoundaryCached.shadows472
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt472
    (AffineBoundaryCached.checked472) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census473 : (AffineBoundaryCached.cert473).seeds.map Prod.fst = AffineSearchData.allowed473 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 473 is a boundary. -/
theorem boundary473 : TopFiberBoundary 0x1600200000000900c10128008002002001000003006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1600200000000900c10128008002002001000003006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete473 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert473).beta ∈
      (AffineBoundaryCached.cert473).seeds.map Prod.fst := by
    rw [census473]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert473) 180 512
    4 AffineBoundaryCached.sheets473 AffineBoundaryCached.shadows473
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt473
    (AffineBoundaryCached.checked473) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census474 : (AffineBoundaryCached.cert474).seeds.map Prod.fst = AffineSearchData.allowed474 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 474 is a boundary. -/
theorem boundary474 : TopFiberBoundary 0x1600600000000000fc0540140020010003000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1600600000000000fc0540140020010003000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete474 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert474).beta ∈
      (AffineBoundaryCached.cert474).seeds.map Prod.fst := by
    rw [census474]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert474) 180 512
    4 AffineBoundaryCached.sheets474 AffineBoundaryCached.shadows474
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt474
    (AffineBoundaryCached.checked474) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census475 : (AffineBoundaryCached.cert475).seeds.map Prod.fst = AffineSearchData.allowed475 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 475 is a boundary. -/
theorem boundary475 : TopFiberBoundary 0x16006000000012004c0440100000010003000030003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x16006000000012004c0440100000010003000030003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete475 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert475).beta ∈
      (AffineBoundaryCached.cert475).seeds.map Prod.fst := by
    rw [census475]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert475) 180 512
    4 AffineBoundaryCached.sheets475 AffineBoundaryCached.shadows475
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt475
    (AffineBoundaryCached.checked475) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census476 : (AffineBoundaryCached.cert476).seeds.map Prod.fst = AffineSearchData.allowed476 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 476 is a boundary. -/
theorem boundary476 : TopFiberBoundary 0x1601080280000000000480140018025003001400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1601080280000000000480140018025003001400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete476 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert476).beta ∈
      (AffineBoundaryCached.cert476).seeds.map Prod.fst := by
    rw [census476]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert476) 180 512
    8 AffineBoundaryCached.sheets476 AffineBoundaryCached.shadows476
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt476
    (AffineBoundaryCached.checked476) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census477 : (AffineBoundaryCached.cert477).seeds.map Prod.fst = AffineSearchData.allowed477 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 477 is a boundary. -/
theorem boundary477 : TopFiberBoundary 0x16014002000000002404c0140010020003001000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x16014002000000002404c0140010020003001000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete477 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert477).beta ∈
      (AffineBoundaryCached.cert477).seeds.map Prod.fst := by
    rw [census477]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert477) 180 512
    8 AffineBoundaryCached.sheets477 AffineBoundaryCached.shadows477
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt477
    (AffineBoundaryCached.checked477) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census478 : (AffineBoundaryCached.cert478).seeds.map Prod.fst = AffineSearchData.allowed478 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 478 is a boundary. -/
theorem boundary478 : TopFiberBoundary 0x16014002000000006c0440140000020003001000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x16014002000000006c0440140000020003001000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete478 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert478).beta ∈
      (AffineBoundaryCached.cert478).seeds.map Prod.fst := by
    rw [census478]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert478) 180 512
    2 AffineBoundaryCached.sheets478 AffineBoundaryCached.shadows478
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt478
    (AffineBoundaryCached.checked478) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census479 : (AffineBoundaryCached.cert479).seeds.map Prod.fst = AffineSearchData.allowed479 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 479 is a boundary. -/
theorem boundary479 : TopFiberBoundary 0x1601400200000002400080140098020003001000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1601400200000002400080140098020003001000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete479 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert479).beta ∈
      (AffineBoundaryCached.cert479).seeds.map Prod.fst := by
    rw [census479]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert479) 180 512
    8 AffineBoundaryCached.sheets479 AffineBoundaryCached.shadows479
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt479
    (AffineBoundaryCached.checked479) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census480 : (AffineBoundaryCached.cert480).seeds.map Prod.fst = AffineSearchData.allowed480 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 480 is a boundary. -/
theorem boundary480 : TopFiberBoundary 0x1601400200001200200480100018020003001030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1601400200001200200480100018020003001030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete480 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert480).beta ∈
      (AffineBoundaryCached.cert480).seeds.map Prod.fst := by
    rw [census480]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert480) 180 512
    8 AffineBoundaryCached.sheets480 AffineBoundaryCached.shadows480
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt480
    (AffineBoundaryCached.checked480) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census481 : (AffineBoundaryCached.cert481).seeds.map Prod.fst = AffineSearchData.allowed481 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 481 is a boundary. -/
theorem boundary481 : TopFiberBoundary 0x1601400200004800800480040018020003001018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1601400200004800800480040018020003001018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete481 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert481).beta ∈
      (AffineBoundaryCached.cert481).seeds.map Prod.fst := by
    rw [census481]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert481) 180 512
    8 AffineBoundaryCached.sheets481 AffineBoundaryCached.shadows481
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt481
    (AffineBoundaryCached.checked481) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census482 : (AffineBoundaryCached.cert482).seeds.map Prod.fst = AffineSearchData.allowed482 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 482 is a boundary. -/
theorem boundary482 : TopFiberBoundary 0x16084012000000000004801400181a0003009000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x16084012000000000004801400181a0003009000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete482 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert482).beta ∈
      (AffineBoundaryCached.cert482).seeds.map Prod.fst := by
    rw [census482]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert482) 180 512
    8 AffineBoundaryCached.sheets482 AffineBoundaryCached.shadows482
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt482
    (AffineBoundaryCached.checked482) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census483 : (AffineBoundaryCached.cert483).seeds.map Prod.fst = AffineSearchData.allowed483 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 483 is a boundary. -/
theorem boundary483 : TopFiberBoundary 0x1680280000000000fc01c000000d000001400000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1680280000000000fc01c000000d000001400000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete483 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert483).beta ∈
      (AffineBoundaryCached.cert483).seeds.map Prod.fst := by
    rw [census483]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert483) 180 512
    8 AffineBoundaryCached.sheets483 AffineBoundaryCached.shadows483
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt483
    (AffineBoundaryCached.checked483) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census484 : (AffineBoundaryCached.cert484).seeds.map Prod.fst = AffineSearchData.allowed484 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 484 is a boundary. -/
theorem boundary484 : TopFiberBoundary 0x1680440088008000000000000035003001800600040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1680440088008000000000000035003001800600040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete484 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert484).beta ∈
      (AffineBoundaryCached.cert484).seeds.map Prod.fst := by
    rw [census484]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert484) 180 512
    8 AffineBoundaryCached.sheets484 AffineBoundaryCached.shadows484
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt484
    (AffineBoundaryCached.checked484) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census485 : (AffineBoundaryCached.cert485).seeds.map Prod.fst = AffineSearchData.allowed485 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 485 is a boundary. -/
theorem boundary485 : TopFiberBoundary 0x1800200000000000ea80a802800d005001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800200000000000ea80a802800d005001000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete485 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert485).beta ∈
      (AffineBoundaryCached.cert485).seeds.map Prod.fst := by
    rw [census485]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert485) 180 512
    2 AffineBoundaryCached.sheets485 AffineBoundaryCached.shadows485
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt485
    (AffineBoundaryCached.checked485) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census486 : (AffineBoundaryCached.cert486).seeds.map Prod.fst = AffineSearchData.allowed486 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 486 is a boundary. -/
theorem boundary486 : TopFiberBoundary 0x18008000000000014c0980140040028004000000033 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x18008000000000014c0980140040028004000000033)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete486 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert486).beta ∈
      (AffineBoundaryCached.cert486).seeds.map Prod.fst := by
    rw [census486]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert486) 180 512
    4 AffineBoundaryCached.sheets486 AffineBoundaryCached.shadows486
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt486
    (AffineBoundaryCached.checked486) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census487 : (AffineBoundaryCached.cert487).seeds.map Prod.fst = AffineSearchData.allowed487 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 487 is a boundary. -/
theorem boundary487 : TopFiberBoundary 0x1800800000000240200b00148010028004000006006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000000240200b00148010028004000006006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete487 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert487).beta ∈
      (AffineBoundaryCached.cert487).seeds.map Prod.fst := by
    rw [census487]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert487) 180 512
    8 AffineBoundaryCached.sheets487 AffineBoundaryCached.shadows487
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt487
    (AffineBoundaryCached.checked487) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census488 : (AffineBoundaryCached.cert488).seeds.map Prod.fst = AffineSearchData.allowed488 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 488 is a boundary. -/
theorem boundary488 : TopFiberBoundary 0x18008000000012004c0b80100000028004000030003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x18008000000012004c0b80100000028004000030003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete488 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert488).beta ∈
      (AffineBoundaryCached.cert488).seeds.map Prod.fst := by
    rw [census488]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert488) 180 512
    4 AffineBoundaryCached.sheets488 AffineBoundaryCached.shadows488
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt488
    (AffineBoundaryCached.checked488) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census489 : (AffineBoundaryCached.cert489).seeds.map Prod.fst = AffineSearchData.allowed489 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 489 is a boundary. -/
theorem boundary489 : TopFiberBoundary 0x1800800000004800a40b00040010028004000018006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000004800a40b00040010028004000018006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete489 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert489).beta ∈
      (AffineBoundaryCached.cert489).seeds.map Prod.fst := by
    rw [census489]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert489) 180 512
    8 AffineBoundaryCached.sheets489 AffineBoundaryCached.shadows489
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt489
    (AffineBoundaryCached.checked489) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census490 : (AffineBoundaryCached.cert490).seeds.map Prod.fst = AffineSearchData.allowed490 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 490 is a boundary. -/
theorem boundary490 : TopFiberBoundary 0x1800800000005a00840b00000010028004000028006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000005a00840b00000010028004000028006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete490 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert490).beta ∈
      (AffineBoundaryCached.cert490).seeds.map Prod.fst := by
    rw [census490]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert490) 180 512
    2 AffineBoundaryCached.sheets490 AffineBoundaryCached.shadows490
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt490
    (AffineBoundaryCached.checked490) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census491 : (AffineBoundaryCached.cert491).seeds.map Prod.fst = AffineSearchData.allowed491 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 491 is a boundary. -/
theorem boundary491 : TopFiberBoundary 0x1800800000005a00a00b40000018028004000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1800800000005a00a00b40000018028004000028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete491 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert491).beta ∈
      (AffineBoundaryCached.cert491).seeds.map Prod.fst := by
    rw [census491]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert491) 180 512
    8 AffineBoundaryCached.sheets491 AffineBoundaryCached.shadows491
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt491
    (AffineBoundaryCached.checked491) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census492 : (AffineBoundaryCached.cert492).seeds.map Prod.fst = AffineSearchData.allowed492 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 492 is a boundary. -/
theorem boundary492 : TopFiberBoundary 0x1801a00200000000240b00140010018004001000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1801a00200000000240b00140010018004001000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete492 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert492).beta ∈
      (AffineBoundaryCached.cert492).seeds.map Prod.fst := by
    rw [census492]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert492) 180 512
    8 AffineBoundaryCached.sheets492 AffineBoundaryCached.shadows492
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt492
    (AffineBoundaryCached.checked492) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census493 : (AffineBoundaryCached.cert493).seeds.map Prod.fst = AffineSearchData.allowed493 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 493 is a boundary. -/
theorem boundary493 : TopFiberBoundary 0x1802c004000000006c0b80140000000004002000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1802c004000000006c0b80140000000004002000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete493 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert493).beta ∈
      (AffineBoundaryCached.cert493).seeds.map Prod.fst := by
    rw [census493]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert493) 180 512
    4 AffineBoundaryCached.sheets493 AffineBoundaryCached.shadows493
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt493
    (AffineBoundaryCached.checked493) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census494 : (AffineBoundaryCached.cert494).seeds.map Prod.fst = AffineSearchData.allowed494 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 494 is a boundary. -/
theorem boundary494 : TopFiberBoundary 0x1802c00400000001040900140050000004002000036 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1802c00400000001040900140050000004002000036)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete494 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert494).beta ∈
      (AffineBoundaryCached.cert494).seeds.map Prod.fst := by
    rw [census494]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert494) 180 512
    4 AffineBoundaryCached.sheets494 AffineBoundaryCached.shadows494
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt494
    (AffineBoundaryCached.checked494) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census495 : (AffineBoundaryCached.cert495).seeds.map Prod.fst = AffineSearchData.allowed495 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 495 is a boundary. -/
theorem boundary495 : TopFiberBoundary 0x1802c00400001200040b00100010000004002030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1802c00400001200040b00100010000004002030006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete495 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert495).beta ∈
      (AffineBoundaryCached.cert495).seeds.map Prod.fst := by
    rw [census495]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert495) 180 512
    2 AffineBoundaryCached.sheets495 AffineBoundaryCached.shadows495
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt495
    (AffineBoundaryCached.checked495) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census496 : (AffineBoundaryCached.cert496).seeds.map Prod.fst = AffineSearchData.allowed496 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 496 is a boundary. -/
theorem boundary496 : TopFiberBoundary 0x1804000800000000480bc0140008030004004000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800000000480bc0140008030004004000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete496 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert496).beta ∈
      (AffineBoundaryCached.cert496).seeds.map Prod.fst := by
    rw [census496]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert496) 180 512
    8 AffineBoundaryCached.sheets496 AffineBoundaryCached.shadows496
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt496
    (AffineBoundaryCached.checked496) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census497 : (AffineBoundaryCached.cert497).seeds.map Prod.fst = AffineSearchData.allowed497 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 497 is a boundary. -/
theorem boundary497 : TopFiberBoundary 0x18040008000000006c0b80140000030004004000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x18040008000000006c0b80140000030004004000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete497 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert497).beta ∈
      (AffineBoundaryCached.cert497).seeds.map Prod.fst := by
    rw [census497]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert497) 180 512
    4 AffineBoundaryCached.sheets497 AffineBoundaryCached.shadows497
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt497
    (AffineBoundaryCached.checked497) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census498 : (AffineBoundaryCached.cert498).seeds.map Prod.fst = AffineSearchData.allowed498 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 498 is a boundary. -/
theorem boundary498 : TopFiberBoundary 0x1804000800000000900a40140038030004004000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800000000900a40140038030004004000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete498 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert498).beta ∈
      (AffineBoundaryCached.cert498).seeds.map Prod.fst := by
    rw [census498]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert498) 180 512
    8 AffineBoundaryCached.sheets498 AffineBoundaryCached.shadows498
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt498
    (AffineBoundaryCached.checked498) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census499 : (AffineBoundaryCached.cert499).seeds.map Prod.fst = AffineSearchData.allowed499 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 499 is a boundary. -/
theorem boundary499 : TopFiberBoundary 0x1804000800000001040900140050030004004000036 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800000001040900140050030004004000036)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete499 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert499).beta ∈
      (AffineBoundaryCached.cert499).seeds.map Prod.fst := by
    rw [census499]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert499) 180 512
    4 AffineBoundaryCached.sheets499 AffineBoundaryCached.shadows499
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt499
    (AffineBoundaryCached.checked499) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census500 : (AffineBoundaryCached.cert500).seeds.map Prod.fst = AffineSearchData.allowed500 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 500 is a boundary. -/
theorem boundary500 : TopFiberBoundary 0x1804000800000001200940140058030004004000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800000001200940140058030004004000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete500 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert500).beta ∈
      (AffineBoundaryCached.cert500).seeds.map Prod.fst := by
    rw [census500]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert500) 180 512
    8 AffineBoundaryCached.sheets500 AffineBoundaryCached.shadows500
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt500
    (AffineBoundaryCached.checked500) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census501 : (AffineBoundaryCached.cert501).seeds.map Prod.fst = AffineSearchData.allowed501 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 501 is a boundary. -/
theorem boundary501 : TopFiberBoundary 0x1804000800000004800340140118030004004000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800000004800340140118030004004000018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete501 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert501).beta ∈
      (AffineBoundaryCached.cert501).seeds.map Prod.fst := by
    rw [census501]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert501) 180 512
    8 AffineBoundaryCached.sheets501 AffineBoundaryCached.shadows501
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt501
    (AffineBoundaryCached.checked501) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census502 : (AffineBoundaryCached.cert502).seeds.map Prod.fst = AffineSearchData.allowed502 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 502 is a boundary. -/
theorem boundary502 : TopFiberBoundary 0x1804000800001200040b00100010030004004030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800001200040b00100010030004004030006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete502 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert502).beta ∈
      (AffineBoundaryCached.cert502).seeds.map Prod.fst := by
    rw [census502]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert502) 180 512
    2 AffineBoundaryCached.sheets502 AffineBoundaryCached.shadows502
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt502
    (AffineBoundaryCached.checked502) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census503 : (AffineBoundaryCached.cert503).seeds.map Prod.fst = AffineSearchData.allowed503 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 503 is a boundary. -/
theorem boundary503 : TopFiberBoundary 0x1804000800001200200b40100018030004004030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800001200200b40100018030004004030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete503 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert503).beta ∈
      (AffineBoundaryCached.cert503).seeds.map Prod.fst := by
    rw [census503]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert503) 180 512
    8 AffineBoundaryCached.sheets503 AffineBoundaryCached.shadows503
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt503
    (AffineBoundaryCached.checked503) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty

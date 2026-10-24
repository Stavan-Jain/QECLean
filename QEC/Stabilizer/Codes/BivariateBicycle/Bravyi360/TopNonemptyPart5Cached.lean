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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census504 : (AffineBoundaryCached.cert504).seeds.map Prod.fst = AffineSearchData.allowed504 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 504 is a boundary. -/
theorem boundary504 : TopFiberBoundary 0x1804000800004800800b40040018030004004018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1804000800004800800b40040018030004004018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete504 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert504).beta ∈
      (AffineBoundaryCached.cert504).seeds.map Prod.fst := by
    rw [census504]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert504) 180 512
    8 AffineBoundaryCached.sheets504 AffineBoundaryCached.shadows504
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt504
    (AffineBoundaryCached.checked504) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census505 : (AffineBoundaryCached.cert505).seeds.map Prod.fst = AffineSearchData.allowed505 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 505 is a boundary. -/
theorem boundary505 : TopFiberBoundary 0x1805200a00000000240b00140010000004005000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1805200a00000000240b00140010000004005000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete505 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert505).beta ∈
      (AffineBoundaryCached.cert505).seeds.map Prod.fst := by
    rw [census505]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert505) 180 512
    2 AffineBoundaryCached.sheets505 AffineBoundaryCached.shadows505
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt505
    (AffineBoundaryCached.checked505) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census506 : (AffineBoundaryCached.cert506).seeds.map Prod.fst = AffineSearchData.allowed506 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 506 is a boundary. -/
theorem boundary506 : TopFiberBoundary 0x1a00200000000000ee00d801800c004001000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1a00200000000000ee00d801800c004001000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete506 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert506).beta ∈
      (AffineBoundaryCached.cert506).seeds.map Prod.fst := by
    rw [census506]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert506) 180 512
    4 AffineBoundaryCached.sheets506 AffineBoundaryCached.shadows506
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt506
    (AffineBoundaryCached.checked506) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census507 : (AffineBoundaryCached.cert507).seeds.map Prod.fst = AffineSearchData.allowed507 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 507 is a boundary. -/
theorem boundary507 : TopFiberBoundary 0x1a00a00000000000fc08c00c0010020005000000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1a00a00000000000fc08c00c0010020005000000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete507 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert507).beta ∈
      (AffineBoundaryCached.cert507).seeds.map Prod.fst := by
    rw [census507]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert507) 180 512
    2 AffineBoundaryCached.sheets507 AffineBoundaryCached.shadows507
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt507
    (AffineBoundaryCached.checked507) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census508 : (AffineBoundaryCached.cert508).seeds.map Prod.fst = AffineSearchData.allowed508 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 508 is a boundary. -/
theorem boundary508 : TopFiberBoundary 0x1a00a00000001200940840080000020005000030005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1a00a00000001200940840080000020005000030005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete508 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert508).beta ∈
      (AffineBoundaryCached.cert508).seeds.map Prod.fst := by
    rw [census508]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert508) 180 512
    2 AffineBoundaryCached.sheets508 AffineBoundaryCached.shadows508
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt508
    (AffineBoundaryCached.checked508) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census509 : (AffineBoundaryCached.cert509).seeds.map Prod.fst = AffineSearchData.allowed509 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 509 is a boundary. -/
theorem boundary509 : TopFiberBoundary 0x1a01800200000000b408400c0000010005001000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1a01800200000000b408400c0000010005001000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete509 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert509).beta ∈
      (AffineBoundaryCached.cert509).seeds.map Prod.fst := by
    rw [census509]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert509) 180 512
    4 AffineBoundaryCached.sheets509 AffineBoundaryCached.shadows509
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt509
    (AffineBoundaryCached.checked509) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census510 : (AffineBoundaryCached.cert510).seeds.map Prod.fst = AffineSearchData.allowed510 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 510 is a boundary. -/
theorem boundary510 : TopFiberBoundary 0x1a06600c000000000009000c0028010005006000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1a06600c000000000009000c0028010005006000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete510 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert510).beta ∈
      (AffineBoundaryCached.cert510).seeds.map Prod.fst := by
    rw [census510]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert510) 180 512
    8 AffineBoundaryCached.sheets510 AffineBoundaryCached.shadows510
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt510
    (AffineBoundaryCached.checked510) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census511 : (AffineBoundaryCached.cert511).seeds.map Prod.fst = AffineSearchData.allowed511 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 511 is a boundary. -/
theorem boundary511 : TopFiberBoundary 0x1b00300000000000fc01c000000b000001800000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1b00300000000000fc01c000000b000001800000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete511 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert511).beta ∈
      (AffineBoundaryCached.cert511).seeds.map Prod.fst := by
    rw [census511]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert511) 180 512
    8 AffineBoundaryCached.sheets511 AffineBoundaryCached.shadows511
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt511
    (AffineBoundaryCached.checked511) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census512 : (AffineBoundaryCached.cert512).seeds.map Prod.fst = AffineSearchData.allowed512 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 512 is a boundary. -/
theorem boundary512 : TopFiberBoundary 0x1c00c00000000000480f40000020038006000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1c00c00000000000480f40000020038006000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete512 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert512).beta ∈
      (AffineBoundaryCached.cert512).seeds.map Prod.fst := by
    rw [census512]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert512) 180 512
    4 AffineBoundaryCached.sheets512 AffineBoundaryCached.shadows512
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt512
    (AffineBoundaryCached.checked512) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census513 : (AffineBoundaryCached.cert513).seeds.map Prod.fst = AffineSearchData.allowed513 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 513 is a boundary. -/
theorem boundary513 : TopFiberBoundary 0x1c01e00200000000000fc0000030008006001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1c01e00200000000000fc0000030008006001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete513 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert513).beta ∈
      (AffineBoundaryCached.cert513).seeds.map Prod.fst := by
    rw [census513]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert513) 180 512
    4 AffineBoundaryCached.sheets513 AffineBoundaryCached.shadows513
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt513
    (AffineBoundaryCached.checked513) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census514 : (AffineBoundaryCached.cert514).seeds.map Prod.fst = AffineSearchData.allowed514 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 514 is a boundary. -/
theorem boundary514 : TopFiberBoundary 0x1c04400800000000480f40000020020006004000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1c04400800000000480f40000020020006004000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete514 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert514).beta ∈
      (AffineBoundaryCached.cert514).seeds.map Prod.fst := by
    rw [census514]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert514) 180 512
    2 AffineBoundaryCached.sheets514 AffineBoundaryCached.shadows514
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt514
    (AffineBoundaryCached.checked514) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census515 : (AffineBoundaryCached.cert515).seeds.map Prod.fst = AffineSearchData.allowed515 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 515 is a boundary. -/
theorem boundary515 : TopFiberBoundary 0x1c40000040000000e70070030008000001200200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x1c40000040000000e70070030008000001200200000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete515 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert515).beta ∈
      (AffineBoundaryCached.cert515).seeds.map Prod.fst := by
    rw [census515]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert515) 180 512
    4 AffineBoundaryCached.sheets515 AffineBoundaryCached.shadows515
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt515
    (AffineBoundaryCached.checked515) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census516 : (AffineBoundaryCached.cert516).seeds.map Prod.fst = AffineSearchData.allowed516 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 516 is a boundary. -/
theorem boundary516 : TopFiberBoundary 0x2000000000008206c00a803001c00100000001b0000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000008206c00a803001c00100000001b0000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete516 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert516).beta ∈
      (AffineBoundaryCached.cert516).seeds.map Prod.fst := by
    rw [census516]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert516) 180 512
    4 AffineBoundaryCached.sheets516 AffineBoundaryCached.shadows516
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt516
    (AffineBoundaryCached.checked516) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census517 : (AffineBoundaryCached.cert517).seeds.map Prod.fst = AffineSearchData.allowed517 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 517 is a boundary. -/
theorem boundary517 : TopFiberBoundary 0x2000000000009006e00a803401c0010000000180000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2000000000009006e00a803401c0010000000180000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete517 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert517).beta ∈
      (AffineBoundaryCached.cert517).seeds.map Prod.fst := by
    rw [census517]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert517) 180 512
    6 AffineBoundaryCached.sheets517 AffineBoundaryCached.shadows517
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt517
    (AffineBoundaryCached.checked517) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census518 : (AffineBoundaryCached.cert518).seeds.map Prod.fst = AffineSearchData.allowed518 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 518 is a boundary. -/
theorem boundary518 : TopFiberBoundary 0x208045805000800000000000002d0006028000c0040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x208045805000800000000000002d0006028000c0040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete518 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert518).beta ∈
      (AffineBoundaryCached.cert518).seeds.map Prod.fst := by
    rw [census518]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert518) 180 512
    8 AffineBoundaryCached.sheets518 AffineBoundaryCached.shadows518
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt518
    (AffineBoundaryCached.checked518) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census519 : (AffineBoundaryCached.cert519).seeds.map Prod.fst = AffineSearchData.allowed519 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 519 is a boundary. -/
theorem boundary519 : TopFiberBoundary 0x2080b4018800800000000000002d000002800e00040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2080b4018800800000000000002d000002800e00040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete519 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert519).beta ∈
      (AffineBoundaryCached.cert519).seeds.map Prod.fst := by
    rw [census519]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert519) 180 512
    2 AffineBoundaryCached.sheets519 AffineBoundaryCached.shadows519
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt519
    (AffineBoundaryCached.checked519) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census520 : (AffineBoundaryCached.cert520).seeds.map Prod.fst = AffineSearchData.allowed520 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 520 is a boundary. -/
theorem boundary520 : TopFiberBoundary 0x2400400000009001fc01c0200010000002000180000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2400400000009001fc01c0200010000002000180000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete520 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert520).beta ∈
      (AffineBoundaryCached.cert520).seeds.map Prod.fst := by
    rw [census520]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert520) 180 512
    8 AffineBoundaryCached.sheets520 AffineBoundaryCached.shadows520
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt520
    (AffineBoundaryCached.checked520) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census521 : (AffineBoundaryCached.cert521).seeds.map Prod.fst = AffineSearchData.allowed521 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 521 is a boundary. -/
theorem boundary521 : TopFiberBoundary 0x24005f8038009001000000200028000002000040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x24005f8038009001000000200028000002000040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete521 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert521).beta ∈
      (AffineBoundaryCached.cert521).seeds.map Prod.fst := by
    rw [census521]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert521) 180 512
    8 AffineBoundaryCached.sheets521 AffineBoundaryCached.shadows521
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt521
    (AffineBoundaryCached.checked521) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census522 : (AffineBoundaryCached.cert522).seeds.map Prod.fst = AffineSearchData.allowed522 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 522 is a boundary. -/
theorem boundary522 : TopFiberBoundary 0x2400bc0188008000000000000028000002c00e00040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x2400bc0188008000000000000028000002c00e00040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete522 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert522).beta ∈
      (AffineBoundaryCached.cert522).seeds.map Prod.fst := by
    rw [census522]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert522) 180 512
    6 AffineBoundaryCached.sheets522 AffineBoundaryCached.shadows522
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt522
    (AffineBoundaryCached.checked522) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census523 : (AffineBoundaryCached.cert523).seeds.map Prod.fst = AffineSearchData.allowed523 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 523 is a boundary. -/
theorem boundary523 : TopFiberBoundary 0x3000000000001200dc0700080038018000000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3000000000001200dc0700080038018000000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete523 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert523).beta ∈
      (AffineBoundaryCached.cert523).seeds.map Prod.fst := by
    rw [census523]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert523) 180 512
    4 AffineBoundaryCached.sheets523 AffineBoundaryCached.shadows523
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt523
    (AffineBoundaryCached.checked523) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census524 : (AffineBoundaryCached.cert524).seeds.map Prod.fst = AffineSearchData.allowed524 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 524 is a boundary. -/
theorem boundary524 : TopFiberBoundary 0x30000000000020820802c005008001800000002d028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30000000000020820802c005008001800000002d028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete524 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert524).beta ∈
      (AffineBoundaryCached.cert524).seeds.map Prod.fst := by
    rw [census524]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert524) 180 512
    8 AffineBoundaryCached.sheets524 AffineBoundaryCached.shadows524
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt524
    (AffineBoundaryCached.checked524) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census525 : (AffineBoundaryCached.cert525).seeds.map Prod.fst = AffineSearchData.allowed525 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 525 is a boundary. -/
theorem boundary525 : TopFiberBoundary 0x3000000000002401280440040050018000000028035 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3000000000002401280440040050018000000028035)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete525 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert525).beta ∈
      (AffineBoundaryCached.cert525).seeds.map Prod.fst := by
    rw [census525]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert525) 180 512
    8 AffineBoundaryCached.sheets525 AffineBoundaryCached.shadows525
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt525
    (AffineBoundaryCached.checked525) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census526 : (AffineBoundaryCached.cert526).seeds.map Prod.fst = AffineSearchData.allowed526 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 526 is a boundary. -/
theorem boundary526 : TopFiberBoundary 0x300000000000240224028004008801800000002802e := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300000000000240224028004008801800000002802e)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete526 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert526).beta ∈
      (AffineBoundaryCached.cert526).seeds.map Prod.fst := by
    rw [census526]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert526) 180 512
    8 AffineBoundaryCached.sheets526 AffineBoundaryCached.shadows526
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt526
    (AffineBoundaryCached.checked526) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census527 : (AffineBoundaryCached.cert527).seeds.map Prod.fst = AffineSearchData.allowed527 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 527 is a boundary. -/
theorem boundary527 : TopFiberBoundary 0x3000000000002406800ac0040180018000000028030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3000000000002406800ac0040180018000000028030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete527 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert527).beta ∈
      (AffineBoundaryCached.cert527).seeds.map Prod.fst := by
    rw [census527]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert527) 180 512
    8 AffineBoundaryCached.sheets527 AffineBoundaryCached.shadows527
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt527
    (AffineBoundaryCached.checked527) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census528 : (AffineBoundaryCached.cert528).seeds.map Prod.fst = AffineSearchData.allowed528 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 528 is a boundary. -/
theorem boundary528 : TopFiberBoundary 0x30000000000032806806c001000001800000001d000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30000000000032806806c001000001800000001d000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete528 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert528).beta ∈
      (AffineBoundaryCached.cert528).seeds.map Prod.fst := by
    rw [census528]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert528) 180 512
    8 AffineBoundaryCached.sheets528 AffineBoundaryCached.shadows528
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt528
    (AffineBoundaryCached.checked528) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census529 : (AffineBoundaryCached.cert529).seeds.map Prod.fst = AffineSearchData.allowed529 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 529 is a boundary. -/
theorem boundary529 : TopFiberBoundary 0x30000000000034406406c000800001800000001e000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30000000000034406406c000800001800000001e000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete529 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert529).beta ∈
      (AffineBoundaryCached.cert529).seeds.map Prod.fst := by
    rw [census529]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert529) 180 512
    8 AffineBoundaryCached.sheets529 AffineBoundaryCached.shadows529
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt529
    (AffineBoundaryCached.checked529) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census530 : (AffineBoundaryCached.cert530).seeds.map Prod.fst = AffineSearchData.allowed530 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 530 is a boundary. -/
theorem boundary530 : TopFiberBoundary 0x3000000000003601080440000050018000000018035 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3000000000003601080440000050018000000018035)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete530 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert530).beta ∈
      (AffineBoundaryCached.cert530).seeds.map Prod.fst := by
    rw [census530]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert530) 180 512
    2 AffineBoundaryCached.sheets530 AffineBoundaryCached.shadows530
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt530
    (AffineBoundaryCached.checked530) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census531 : (AffineBoundaryCached.cert531).seeds.map Prod.fst = AffineSearchData.allowed531 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 531 is a boundary. -/
theorem boundary531 : TopFiberBoundary 0x300000000000360204028000008801800000001802e := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300000000000360204028000008801800000001802e)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete531 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert531).beta ∈
      (AffineBoundaryCached.cert531).seeds.map Prod.fst := by
    rw [census531]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert531) 180 512
    2 AffineBoundaryCached.sheets531 AffineBoundaryCached.shadows531
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt531
    (AffineBoundaryCached.checked531) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census532 : (AffineBoundaryCached.cert532).seeds.map Prod.fst = AffineSearchData.allowed532 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 532 is a boundary. -/
theorem boundary532 : TopFiberBoundary 0x3000000000010402080640440010018000000168005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3000000000010402080640440010018000000168005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete532 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert532).beta ∈
      (AffineBoundaryCached.cert532).seeds.map Prod.fst := by
    rw [census532]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert532) 180 512
    8 AffineBoundaryCached.sheets532 AffineBoundaryCached.shadows532
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt532
    (AffineBoundaryCached.checked532) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census533 : (AffineBoundaryCached.cert533).seeds.map Prod.fst = AffineSearchData.allowed533 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 533 is a boundary. -/
theorem boundary533 : TopFiberBoundary 0x30000000000116026006c0400000018000000158000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30000000000116026006c0400000018000000158000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete533 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert533).beta ∈
      (AffineBoundaryCached.cert533).seeds.map Prod.fst := by
    rw [census533]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert533) 180 512
    8 AffineBoundaryCached.sheets533 AffineBoundaryCached.shadows533
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt533
    (AffineBoundaryCached.checked533) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census534 : (AffineBoundaryCached.cert534).seeds.map Prod.fst = AffineSearchData.allowed534 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 534 is a boundary. -/
theorem boundary534 : TopFiberBoundary 0x3001200200002400080640040010028000001028005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3001200200002400080640040010028000001028005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete534 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert534).beta ∈
      (AffineBoundaryCached.cert534).seeds.map Prod.fst := by
    rw [census534]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert534) 180 512
    8 AffineBoundaryCached.sheets534 AffineBoundaryCached.shadows534
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt534
    (AffineBoundaryCached.checked534) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census535 : (AffineBoundaryCached.cert535).seeds.map Prod.fst = AffineSearchData.allowed535 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 535 is a boundary. -/
theorem boundary535 : TopFiberBoundary 0x30012002000036006006c0000000028000001018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30012002000036006006c0000000028000001018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete535 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert535).beta ∈
      (AffineBoundaryCached.cert535).seeds.map Prod.fst := by
    rw [census535]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert535) 180 512
    8 AffineBoundaryCached.sheets535 AffineBoundaryCached.shadows535
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt535
    (AffineBoundaryCached.checked535) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census536 : (AffineBoundaryCached.cert536).seeds.map Prod.fst = AffineSearchData.allowed536 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 536 is a boundary. -/
theorem boundary536 : TopFiberBoundary 0x3002400400002400080640040010030000002028005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3002400400002400080640040010030000002028005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete536 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert536).beta ∈
      (AffineBoundaryCached.cert536).seeds.map Prod.fst := by
    rw [census536]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert536) 180 512
    8 AffineBoundaryCached.sheets536 AffineBoundaryCached.shadows536
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt536
    (AffineBoundaryCached.checked536) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census537 : (AffineBoundaryCached.cert537).seeds.map Prod.fst = AffineSearchData.allowed537 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 537 is a boundary. -/
theorem boundary537 : TopFiberBoundary 0x30024004000036006006c0000000030000002018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30024004000036006006c0000000030000002018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete537 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert537).beta ∈
      (AffineBoundaryCached.cert537).seeds.map Prod.fst := by
    rw [census537]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert537) 180 512
    8 AffineBoundaryCached.sheets537 AffineBoundaryCached.shadows537
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt537
    (AffineBoundaryCached.checked537) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census538 : (AffineBoundaryCached.cert538).seeds.map Prod.fst = AffineSearchData.allowed538 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 538 is a boundary. -/
theorem boundary538 : TopFiberBoundary 0x30032806800000000006c00c0000005000003400000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30032806800000000006c00c0000005000003400000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete538 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert538).beta ∈
      (AffineBoundaryCached.cert538).seeds.map Prod.fst := by
    rw [census538]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert538) 180 512
    8 AffineBoundaryCached.sheets538 AffineBoundaryCached.shadows538
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt538
    (AffineBoundaryCached.checked538) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census539 : (AffineBoundaryCached.cert539).seeds.map Prod.fst = AffineSearchData.allowed539 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 539 is a boundary. -/
theorem boundary539 : TopFiberBoundary 0x30034406400000000006c00c0000006000003200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30034406400000000006c00c0000006000003200000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete539 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert539).beta ∈
      (AffineBoundaryCached.cert539).seeds.map Prod.fst := by
    rw [census539]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert539) 180 512
    8 AffineBoundaryCached.sheets539 AffineBoundaryCached.shadows539
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt539
    (AffineBoundaryCached.checked539) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census540 : (AffineBoundaryCached.cert540).seeds.map Prod.fst = AffineSearchData.allowed540 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 540 is a boundary. -/
theorem boundary540 : TopFiberBoundary 0x30036006000000002406800c0008000000003000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000000002406800c0008000000003000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete540 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert540).beta ∈
      (AffineBoundaryCached.cert540).seeds.map Prod.fst := by
    rw [census540]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert540) 180 512
    8 AffineBoundaryCached.sheets540 AffineBoundaryCached.shadows540
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt540
    (AffineBoundaryCached.checked540) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census541 : (AffineBoundaryCached.cert541).seeds.map Prod.fst = AffineSearchData.allowed541 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 541 is a boundary. -/
theorem boundary541 : TopFiberBoundary 0x30036006000000004806400c0010000000003000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000000004806400c0010000000003000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete541 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert541).beta ∈
      (AffineBoundaryCached.cert541).seeds.map Prod.fst := by
    rw [census541]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert541) 180 512
    8 AffineBoundaryCached.sheets541 AffineBoundaryCached.shadows541
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt541
    (AffineBoundaryCached.checked541) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census542 : (AffineBoundaryCached.cert542).seeds.map Prod.fst = AffineSearchData.allowed542 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 542 is a boundary. -/
theorem boundary542 : TopFiberBoundary 0x30036006000000012004c00c0040000000003000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000000012004c00c0040000000003000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete542 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert542).beta ∈
      (AffineBoundaryCached.cert542).seeds.map Prod.fst := by
    rw [census542]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert542) 180 512
    8 AffineBoundaryCached.sheets542 AffineBoundaryCached.shadows542
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt542
    (AffineBoundaryCached.checked542) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census543 : (AffineBoundaryCached.cert543).seeds.map Prod.fst = AffineSearchData.allowed543 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 543 is a boundary. -/
theorem boundary543 : TopFiberBoundary 0x30036006000000024002c00c0080000000003000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000000024002c00c0080000000003000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete543 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert543).beta ∈
      (AffineBoundaryCached.cert543).seeds.map Prod.fst := by
    rw [census543]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert543) 180 512
    8 AffineBoundaryCached.sheets543 AffineBoundaryCached.shadows543
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt543
    (AffineBoundaryCached.checked543) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census544 : (AffineBoundaryCached.cert544).seeds.map Prod.fst = AffineSearchData.allowed544 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 544 is a boundary. -/
theorem boundary544 : TopFiberBoundary 0x30036006000012002006c0080000000000003030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000012002006c0080000000000003030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete544 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert544).beta ∈
      (AffineBoundaryCached.cert544).seeds.map Prod.fst := by
    rw [census544]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert544) 180 512
    8 AffineBoundaryCached.sheets544 AffineBoundaryCached.shadows544
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt544
    (AffineBoundaryCached.checked544) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census545 : (AffineBoundaryCached.cert545).seeds.map Prod.fst = AffineSearchData.allowed545 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 545 is a boundary. -/
theorem boundary545 : TopFiberBoundary 0x30036006000024004006c0040000000000003028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30036006000024004006c0040000000000003028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete545 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert545).beta ∈
      (AffineBoundaryCached.cert545).seeds.map Prod.fst := by
    rw [census545]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert545) 180 512
    8 AffineBoundaryCached.sheets545 AffineBoundaryCached.shadows545
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt545
    (AffineBoundaryCached.checked545) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census546 : (AffineBoundaryCached.cert546).seeds.map Prod.fst = AffineSearchData.allowed546 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 546 is a boundary. -/
theorem boundary546 : TopFiberBoundary 0x30048008000024032000c00400c0000000004028018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30048008000024032000c00400c0000000004028018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete546 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert546).beta ∈
      (AffineBoundaryCached.cert546).seeds.map Prod.fst := by
    rw [census546]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert546) 180 512
    4 AffineBoundaryCached.sheets546 AffineBoundaryCached.shadows546
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt546
    (AffineBoundaryCached.checked546) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census547 : (AffineBoundaryCached.cert547).seeds.map Prod.fst = AffineSearchData.allowed547 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 547 is a boundary. -/
theorem boundary547 : TopFiberBoundary 0x3004800800003600280640000010000000004018005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3004800800003600280640000010000000004018005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete547 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert547).beta ∈
      (AffineBoundaryCached.cert547).seeds.map Prod.fst := by
    rw [census547]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert547) 180 512
    2 AffineBoundaryCached.sheets547 AffineBoundaryCached.shadows547
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt547
    (AffineBoundaryCached.checked547) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census548 : (AffineBoundaryCached.cert548).seeds.map Prod.fst = AffineSearchData.allowed548 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 548 is a boundary. -/
theorem boundary548 : TopFiberBoundary 0x3004800800003600440680000008000000004018006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3004800800003600440680000008000000004018006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete548 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert548).beta ∈
      (AffineBoundaryCached.cert548).seeds.map Prod.fst := by
    rw [census548]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert548) 180 512
    4 AffineBoundaryCached.sheets548 AffineBoundaryCached.shadows548
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt548
    (AffineBoundaryCached.checked548) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census549 : (AffineBoundaryCached.cert549).seeds.map Prod.fst = AffineSearchData.allowed549 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 549 is a boundary. -/
theorem boundary549 : TopFiberBoundary 0x30048008000036014004c0000040000000004018030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30048008000036014004c0000040000000004018030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete549 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert549).beta ∈
      (AffineBoundaryCached.cert549).seeds.map Prod.fst := by
    rw [census549]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert549) 180 512
    4 AffineBoundaryCached.sheets549 AffineBoundaryCached.shadows549
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt549
    (AffineBoundaryCached.checked549) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census550 : (AffineBoundaryCached.cert550).seeds.map Prod.fst = AffineSearchData.allowed550 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 550 is a boundary. -/
theorem boundary550 : TopFiberBoundary 0x30048008000036022002c0000080000000004018028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30048008000036022002c0000080000000004018028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete550 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert550).beta ∈
      (AffineBoundaryCached.cert550).seeds.map Prod.fst := by
    rw [census550]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert550) 180 512
    2 AffineBoundaryCached.sheets550 AffineBoundaryCached.shadows550
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt550
    (AffineBoundaryCached.checked550) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census551 : (AffineBoundaryCached.cert551).seeds.map Prod.fst = AffineSearchData.allowed551 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 551 is a boundary. -/
theorem boundary551 : TopFiberBoundary 0x3004800800007e00e006c0100000000000004000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3004800800007e00e006c0100000000000004000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete551 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert551).beta ∈
      (AffineBoundaryCached.cert551).seeds.map Prod.fst := by
    rw [census551]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert551) 180 512
    2 AffineBoundaryCached.sheets551 AffineBoundaryCached.shadows551
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt551
    (AffineBoundaryCached.checked551) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census552 : (AffineBoundaryCached.cert552).seeds.map Prod.fst = AffineSearchData.allowed552 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 552 is a boundary. -/
theorem boundary552 : TopFiberBoundary 0x30048008000104000002c0440080000000004168028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30048008000104000002c0440080000000004168028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete552 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert552).beta ∈
      (AffineBoundaryCached.cert552).seeds.map Prod.fst := by
    rw [census552]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert552) 180 512
    4 AffineBoundaryCached.sheets552 AffineBoundaryCached.shadows552
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt552
    (AffineBoundaryCached.checked552) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census553 : (AffineBoundaryCached.cert553).seeds.map Prod.fst = AffineSearchData.allowed553 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 553 is a boundary. -/
theorem boundary553 : TopFiberBoundary 0x30052002000000000047c06000c0108020001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30052002000000000047c06000c0108020001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete553 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert553).beta ∈
      (AffineBoundaryCached.cert553).seeds.map Prod.fst := by
    rw [census553]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert553) 180 512
    4 AffineBoundaryCached.sheets553 AffineBoundaryCached.shadows553
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt553
    (AffineBoundaryCached.checked553) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census554 : (AffineBoundaryCached.cert554).seeds.map Prod.fst = AffineSearchData.allowed554 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 554 is a boundary. -/
theorem boundary554 : TopFiberBoundary 0x30064004000000000047c06000c0110020002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30064004000000000047c06000c0110020002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete554 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert554).beta ∈
      (AffineBoundaryCached.cert554).seeds.map Prod.fst := by
    rw [census554]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert554) 180 512
    4 AffineBoundaryCached.sheets554 AffineBoundaryCached.shadows554
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt554
    (AffineBoundaryCached.checked554) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census555 : (AffineBoundaryCached.cert555).seeds.map Prod.fst = AffineSearchData.allowed555 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 555 is a boundary. -/
theorem boundary555 : TopFiberBoundary 0x300a6016000000000006c00c000018000000b000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x300a6016000000000006c00c000018000000b000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete555 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert555).beta ∈
      (AffineBoundaryCached.cert555).seeds.map Prod.fst := by
    rw [census555]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert555) 180 512
    8 AffineBoundaryCached.sheets555 AffineBoundaryCached.shadows555
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt555
    (AffineBoundaryCached.checked555) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census556 : (AffineBoundaryCached.cert556).seeds.map Prod.fst = AffineSearchData.allowed556 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 556 is a boundary. -/
theorem boundary556 : TopFiberBoundary 0x30116026000000000006c00c0000140000013000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30116026000000000006c00c0000140000013000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete556 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert556).beta ∈
      (AffineBoundaryCached.cert556).seeds.map Prod.fst := by
    rw [census556]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert556) 180 512
    8 AffineBoundaryCached.sheets556 AffineBoundaryCached.shadows556
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt556
    (AffineBoundaryCached.checked556) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census557 : (AffineBoundaryCached.cert557).seeds.map Prod.fst = AffineSearchData.allowed557 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 557 is a boundary. -/
theorem boundary557 : TopFiberBoundary 0x30404000400000000900a802801c004003200200000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30404000400000000900a802801c004003200200000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete557 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert557).beta ∈
      (AffineBoundaryCached.cert557).seeds.map Prod.fst := by
    rw [census557]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert557) 180 512
    4 AffineBoundaryCached.sheets557 AffineBoundaryCached.shadows557
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt557
    (AffineBoundaryCached.checked557) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census558 : (AffineBoundaryCached.cert558).seeds.map Prod.fst = AffineSearchData.allowed558 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 558 is a boundary. -/
theorem boundary558 : TopFiberBoundary 0x30406400000000000900a802801c002003200000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30406400000000000900a802801c002003200000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete558 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert558).beta ∈
      (AffineBoundaryCached.cert558).seeds.map Prod.fst := by
    rw [census558]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert558) 180 512
    10 AffineBoundaryCached.sheets558 AffineBoundaryCached.shadows558
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt558
    (AffineBoundaryCached.checked558) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census559 : (AffineBoundaryCached.cert559).seeds.map Prod.fst = AffineSearchData.allowed559 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 559 is a boundary. -/
theorem boundary559 : TopFiberBoundary 0x30c09009e000002000000400001b000000000800900 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x30c09009e000002000000400001b000000000800900)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete559 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert559).beta ∈
      (AffineBoundaryCached.cert559).seeds.map Prod.fst := by
    rw [census559]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert559) 180 512
    4 AffineBoundaryCached.sheets559 AffineBoundaryCached.shadows559
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt559
    (AffineBoundaryCached.checked559) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census560 : (AffineBoundaryCached.cert560).seeds.map Prod.fst = AffineSearchData.allowed560 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 560 is a boundary. -/
theorem boundary560 : TopFiberBoundary 0x3100900000000000000fc000001b038004800000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3100900000000000000fc000001b038004800000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete560 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert560).beta ∈
      (AffineBoundaryCached.cert560).seeds.map Prod.fst := by
    rw [census560]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert560) 180 512
    6 AffineBoundaryCached.sheets560 AffineBoundaryCached.shadows560
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt560
    (AffineBoundaryCached.checked560) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census561 : (AffineBoundaryCached.cert561).seeds.map Prod.fst = AffineSearchData.allowed561 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 561 is a boundary. -/
theorem boundary561 : TopFiberBoundary 0x3104100800000000000fc000001b020004804000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3104100800000000000fc000001b020004804000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete561 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert561).beta ∈
      (AffineBoundaryCached.cert561).seeds.map Prod.fst := by
    rw [census561]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert561) 180 512
    2 AffineBoundaryCached.sheets561 AffineBoundaryCached.shadows561
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt561
    (AffineBoundaryCached.checked561) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census562 : (AffineBoundaryCached.cert562).seeds.map Prod.fst = AffineSearchData.allowed562 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 562 is a boundary. -/
theorem boundary562 : TopFiberBoundary 0x3200200000001200dc0540100008010001000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3200200000001200dc0540100008010001000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete562 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert562).beta ∈
      (AffineBoundaryCached.cert562).seeds.map Prod.fst := by
    rw [census562]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert562) 180 512
    2 AffineBoundaryCached.sheets562 AffineBoundaryCached.shadows562
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt562
    (AffineBoundaryCached.checked562) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census563 : (AffineBoundaryCached.cert563).seeds.map Prod.fst = AffineSearchData.allowed563 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 563 is a boundary. -/
theorem boundary563 : TopFiberBoundary 0x320020000000410048050006000001000100001b006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x320020000000410048050006000001000100001b006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete563 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert563).beta ∈
      (AffineBoundaryCached.cert563).seeds.map Prod.fst := by
    rw [census563]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert563) 180 512
    4 AffineBoundaryCached.sheets563 AffineBoundaryCached.shadows563
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt563
    (AffineBoundaryCached.checked563) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census564 : (AffineBoundaryCached.cert564).seeds.map Prod.fst = AffineSearchData.allowed564 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 564 is a boundary. -/
theorem boundary564 : TopFiberBoundary 0x3200200000005a00780500000000010001000028006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3200200000005a00780500000000010001000028006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete564 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert564).beta ∈
      (AffineBoundaryCached.cert564).seeds.map Prod.fst := by
    rw [census564]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert564) 180 512
    4 AffineBoundaryCached.sheets564 AffineBoundaryCached.shadows564
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt564
    (AffineBoundaryCached.checked564) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census565 : (AffineBoundaryCached.cert565).seeds.map Prod.fst = AffineSearchData.allowed565 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 565 is a boundary. -/
theorem boundary565 : TopFiberBoundary 0x3200200000006c001805000c0000010001000030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3200200000006c001805000c0000010001000030006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete565 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert565).beta ∈
      (AffineBoundaryCached.cert565).seeds.map Prod.fst := by
    rw [census565]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert565) 180 512
    4 AffineBoundaryCached.sheets565 AffineBoundaryCached.shadows565
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt565
    (AffineBoundaryCached.checked565) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census566 : (AffineBoundaryCached.cert566).seeds.map Prod.fst = AffineSearchData.allowed566 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 566 is a boundary. -/
theorem boundary566 : TopFiberBoundary 0x3200600000000000650068028002002003000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3200600000000000650068028002002003000000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete566 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert566).beta ∈
      (AffineBoundaryCached.cert566).seeds.map Prod.fst := by
    rw [census566]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert566) 180 512
    4 AffineBoundaryCached.sheets566 AffineBoundaryCached.shadows566
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt566
    (AffineBoundaryCached.checked566) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census567 : (AffineBoundaryCached.cert567).seeds.map Prod.fst = AffineSearchData.allowed567 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 567 is a boundary. -/
theorem boundary567 : TopFiberBoundary 0x3201000200000000fc0540140008020001001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3201000200000000fc0540140008020001001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete567 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert567).beta ∈
      (AffineBoundaryCached.cert567).seeds.map Prod.fst := by
    rw [census567]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert567) 180 512
    4 AffineBoundaryCached.sheets567 AffineBoundaryCached.shadows567
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt567
    (AffineBoundaryCached.checked567) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census568 : (AffineBoundaryCached.cert568).seeds.map Prod.fst = AffineSearchData.allowed568 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 568 is a boundary. -/
theorem boundary568 : TopFiberBoundary 0x3201000200004800100580040010020001001018003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3201000200004800100580040010020001001018003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete568 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert568).beta ∈
      (AffineBoundaryCached.cert568).seeds.map Prod.fst := by
    rw [census568]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert568) 180 512
    10 AffineBoundaryCached.sheets568 AffineBoundaryCached.shadows568
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt568
    (AffineBoundaryCached.checked568) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census569 : (AffineBoundaryCached.cert569).seeds.map Prod.fst = AffineSearchData.allowed569 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 569 is a boundary. -/
theorem boundary569 : TopFiberBoundary 0x3201000200004800580500040000020001001018006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3201000200004800580500040000020001001018006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete569 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert569).beta ∈
      (AffineBoundaryCached.cert569).seeds.map Prod.fst := by
    rw [census569]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert569) 180 512
    4 AffineBoundaryCached.sheets569 AffineBoundaryCached.shadows569
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt569
    (AffineBoundaryCached.checked569) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census570 : (AffineBoundaryCached.cert570).seeds.map Prod.fst = AffineSearchData.allowed570 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 570 is a boundary. -/
theorem boundary570 : TopFiberBoundary 0x34004000000024002c0280100030008002000028003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x34004000000024002c0280100030008002000028003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete570 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert570).beta ∈
      (AffineBoundaryCached.cert570).seeds.map Prod.fst := by
    rw [census570]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert570) 180 512
    8 AffineBoundaryCached.sheets570 AffineBoundaryCached.shadows570
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt570
    (AffineBoundaryCached.checked570) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census571 : (AffineBoundaryCached.cert571).seeds.map Prod.fst = AffineSearchData.allowed571 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 571 is a boundary. -/
theorem boundary571 : TopFiberBoundary 0x3400400000002400bc0380100010008002000028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3400400000002400bc0380100010008002000028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete571 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert571).beta ∈
      (AffineBoundaryCached.cert571).seeds.map Prod.fst := by
    rw [census571]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert571) 180 512
    2 AffineBoundaryCached.sheets571 AffineBoundaryCached.shadows571
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt571
    (AffineBoundaryCached.checked571) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census572 : (AffineBoundaryCached.cert572).seeds.map Prod.fst = AffineSearchData.allowed572 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 572 is a boundary. -/
theorem boundary572 : TopFiberBoundary 0x34004000000048007c0380080010008002000018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x34004000000048007c0380080010008002000018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete572 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert572).beta ∈
      (AffineBoundaryCached.cert572).seeds.map Prod.fst := by
    rw [census572]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert572) 180 512
    4 AffineBoundaryCached.sheets572 AffineBoundaryCached.shadows572
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt572
    (AffineBoundaryCached.checked572) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census573 : (AffineBoundaryCached.cert573).seeds.map Prod.fst = AffineSearchData.allowed573 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 573 is a boundary. -/
theorem boundary573 : TopFiberBoundary 0x3400400000006c003c0380000010008002000030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3400400000006c003c0380000010008002000030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete573 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert573).beta ∈
      (AffineBoundaryCached.cert573).seeds.map Prod.fst := by
    rw [census573]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert573) 180 512
    2 AffineBoundaryCached.sheets573 AffineBoundaryCached.shadows573
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt573
    (AffineBoundaryCached.checked573) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census574 : (AffineBoundaryCached.cert574).seeds.map Prod.fst = AffineSearchData.allowed574 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 574 is a boundary. -/
theorem boundary574 : TopFiberBoundary 0x3400400000007e00540300040000008002000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3400400000007e00540300040000008002000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete574 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert574).beta ∈
      (AffineBoundaryCached.cert574).seeds.map Prod.fst := by
    rw [census574]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert574) 180 512
    2 AffineBoundaryCached.sheets574 AffineBoundaryCached.shadows574
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt574
    (AffineBoundaryCached.checked574) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census575 : (AffineBoundaryCached.cert575).seeds.map Prod.fst = AffineSearchData.allowed575 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 575 is a boundary. -/
theorem boundary575 : TopFiberBoundary 0x34006000000000006880b0030001001003000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x34006000000000006880b0030001001003000000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete575 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert575).beta ∈
      (AffineBoundaryCached.cert575).seeds.map Prod.fst := by
    rw [census575]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert575) 180 512
    4 AffineBoundaryCached.sheets575 AffineBoundaryCached.shadows575
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt575
    (AffineBoundaryCached.checked575) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census576 : (AffineBoundaryCached.cert576).seeds.map Prod.fst = AffineSearchData.allowed576 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 576 is a boundary. -/
theorem boundary576 : TopFiberBoundary 0x3402000400000000fc0380180010020002002000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3402000400000000fc0380180010020002002000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete576 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert576).beta ∈
      (AffineBoundaryCached.cert576).seeds.map Prod.fst := by
    rw [census576]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert576) 180 512
    4 AffineBoundaryCached.sheets576 AffineBoundaryCached.shadows576
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt576
    (AffineBoundaryCached.checked576) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census577 : (AffineBoundaryCached.cert577).seeds.map Prod.fst = AffineSearchData.allowed577 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 577 is a boundary. -/
theorem boundary577 : TopFiberBoundary 0x36014002000000006c00c0000000030003001000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x36014002000000006c00c0000000030003001000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete577 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert577).beta ∈
      (AffineBoundaryCached.cert577).seeds.map Prod.fst := by
    rw [census577]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert577) 180 512
    8 AffineBoundaryCached.sheets577 AffineBoundaryCached.shadows577
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt577
    (AffineBoundaryCached.checked577) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census578 : (AffineBoundaryCached.cert578).seeds.map Prod.fst = AffineSearchData.allowed578 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 578 is a boundary. -/
theorem boundary578 : TopFiberBoundary 0x36022004000000006c00c0000000028003002000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x36022004000000006c00c0000000028003002000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete578 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert578).beta ∈
      (AffineBoundaryCached.cert578).seeds.map Prod.fst := by
    rw [census578]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert578) 180 512
    8 AffineBoundaryCached.sheets578 AffineBoundaryCached.shadows578
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt578
    (AffineBoundaryCached.checked578) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census579 : (AffineBoundaryCached.cert579).seeds.map Prod.fst = AffineSearchData.allowed579 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 579 is a boundary. -/
theorem boundary579 : TopFiberBoundary 0x38008000000000014c0d00000040038004000000033 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38008000000000014c0d00000040038004000000033)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete579 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert579).beta ∈
      (AffineBoundaryCached.cert579).seeds.map Prod.fst := by
    rw [census579]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert579) 180 512
    2 AffineBoundaryCached.sheets579 AffineBoundaryCached.shadows579
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt579
    (AffineBoundaryCached.checked579) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census580 : (AffineBoundaryCached.cert580).seeds.map Prod.fst = AffineSearchData.allowed580 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 580 is a boundary. -/
theorem boundary580 : TopFiberBoundary 0x38008000000000022c0b0000008003800400000002b := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38008000000000022c0b0000008003800400000002b)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete580 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert580).beta ∈
      (AffineBoundaryCached.cert580).seeds.map Prod.fst := by
    rw [census580]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert580) 180 512
    2 AffineBoundaryCached.sheets580 AffineBoundaryCached.shadows580
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt580
    (AffineBoundaryCached.checked580) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census581 : (AffineBoundaryCached.cert581).seeds.map Prod.fst = AffineSearchData.allowed581 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 581 is a boundary. -/
theorem boundary581 : TopFiberBoundary 0x38008000000000030c09000000c003800400000001b := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38008000000000030c09000000c003800400000001b)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete581 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert581).beta ∈
      (AffineBoundaryCached.cert581).seeds.map Prod.fst := by
    rw [census581]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert581) 180 512
    2 AffineBoundaryCached.sheets581 AffineBoundaryCached.shadows581
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt581
    (AffineBoundaryCached.checked581) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census582 : (AffineBoundaryCached.cert582).seeds.map Prod.fst = AffineSearchData.allowed582 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 582 is a boundary. -/
theorem boundary582 : TopFiberBoundary 0x3801a00200000000240f80000010008004001000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3801a00200000000240f80000010008004001000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete582 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert582).beta ∈
      (AffineBoundaryCached.cert582).seeds.map Prod.fst := by
    rw [census582]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert582) 180 512
    2 AffineBoundaryCached.sheets582 AffineBoundaryCached.shadows582
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt582
    (AffineBoundaryCached.checked582) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census583 : (AffineBoundaryCached.cert583).seeds.map Prod.fst = AffineSearchData.allowed583 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 583 is a boundary. -/
theorem boundary583 : TopFiberBoundary 0x3801a00200000000480f40000008008004001000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3801a00200000000480f40000008008004001000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete583 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert583).beta ∈
      (AffineBoundaryCached.cert583).seeds.map Prod.fst := by
    rw [census583]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert583) 180 512
    4 AffineBoundaryCached.sheets583 AffineBoundaryCached.shadows583
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt583
    (AffineBoundaryCached.checked583) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census584 : (AffineBoundaryCached.cert584).seeds.map Prod.fst = AffineSearchData.allowed584 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 584 is a boundary. -/
theorem boundary584 : TopFiberBoundary 0x3801a002000000006c0f00000000008004001000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3801a002000000006c0f00000000008004001000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete584 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert584).beta ∈
      (AffineBoundaryCached.cert584).seeds.map Prod.fst := by
    rw [census584]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert584) 180 512
    2 AffineBoundaryCached.sheets584 AffineBoundaryCached.shadows584
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt584
    (AffineBoundaryCached.checked584) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census585 : (AffineBoundaryCached.cert585).seeds.map Prod.fst = AffineSearchData.allowed585 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 585 is a boundary. -/
theorem boundary585 : TopFiberBoundary 0x3802c00400000000480f40000008010004002000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3802c00400000000480f40000008010004002000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete585 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert585).beta ∈
      (AffineBoundaryCached.cert585).seeds.map Prod.fst := by
    rw [census585]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert585) 180 512
    2 AffineBoundaryCached.sheets585 AffineBoundaryCached.shadows585
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt585
    (AffineBoundaryCached.checked585) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census586 : (AffineBoundaryCached.cert586).seeds.map Prod.fst = AffineSearchData.allowed586 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 586 is a boundary. -/
theorem boundary586 : TopFiberBoundary 0x3804000800000000900ec0000038020004004000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000000900ec0000038020004004000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete586 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert586).beta ∈
      (AffineBoundaryCached.cert586).seeds.map Prod.fst := by
    rw [census586]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert586) 180 512
    2 AffineBoundaryCached.sheets586 AffineBoundaryCached.shadows586
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt586
    (AffineBoundaryCached.checked586) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census587 : (AffineBoundaryCached.cert587).seeds.map Prod.fst = AffineSearchData.allowed587 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 587 is a boundary. -/
theorem boundary587 : TopFiberBoundary 0x3804000800000000d80e40000028020004004000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000000d80e40000028020004004000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete587 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert587).beta ∈
      (AffineBoundaryCached.cert587).seeds.map Prod.fst := by
    rw [census587]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert587) 180 512
    2 AffineBoundaryCached.sheets587 AffineBoundaryCached.shadows587
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt587
    (AffineBoundaryCached.checked587) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census588 : (AffineBoundaryCached.cert588).seeds.map Prod.fst = AffineSearchData.allowed588 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 588 is a boundary. -/
theorem boundary588 : TopFiberBoundary 0x3804000800000001040d80000050020004004000036 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000001040d80000050020004004000036)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete588 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert588).beta ∈
      (AffineBoundaryCached.cert588).seeds.map Prod.fst := by
    rw [census588]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert588) 180 512
    2 AffineBoundaryCached.sheets588 AffineBoundaryCached.shadows588
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt588
    (AffineBoundaryCached.checked588) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census589 : (AffineBoundaryCached.cert589).seeds.map Prod.fst = AffineSearchData.allowed589 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 589 is a boundary. -/
theorem boundary589 : TopFiberBoundary 0x3804000800000001200dc0000058020004004000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000001200dc0000058020004004000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete589 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert589).beta ∈
      (AffineBoundaryCached.cert589).seeds.map Prod.fst := by
    rw [census589]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert589) 180 512
    2 AffineBoundaryCached.sheets589 AffineBoundaryCached.shadows589
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt589
    (AffineBoundaryCached.checked589) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census590 : (AffineBoundaryCached.cert590).seeds.map Prod.fst = AffineSearchData.allowed590 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 590 is a boundary. -/
theorem boundary590 : TopFiberBoundary 0x38040008000000014c0d00000040020004004000033 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38040008000000014c0d00000040020004004000033)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete590 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert590).beta ∈
      (AffineBoundaryCached.cert590).seeds.map Prod.fst := by
    rw [census590]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert590) 180 512
    2 AffineBoundaryCached.sheets590 AffineBoundaryCached.shadows590
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt590
    (AffineBoundaryCached.checked590) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census591 : (AffineBoundaryCached.cert591).seeds.map Prod.fst = AffineSearchData.allowed591 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 591 is a boundary. -/
theorem boundary591 : TopFiberBoundary 0x3804000800000002080b4000008802000400400002d := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000002080b4000008802000400400002d)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete591 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert591).beta ∈
      (AffineBoundaryCached.cert591).seeds.map Prod.fst := by
    rw [census591]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert591) 180 512
    2 AffineBoundaryCached.sheets591 AffineBoundaryCached.shadows591
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt591
    (AffineBoundaryCached.checked591) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census592 : (AffineBoundaryCached.cert592).seeds.map Prod.fst = AffineSearchData.allowed592 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 592 is a boundary. -/
theorem boundary592 : TopFiberBoundary 0x38040008000000022c0b0000008002000400400002b := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38040008000000022c0b0000008002000400400002b)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete592 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert592).beta ∈
      (AffineBoundaryCached.cert592).seeds.map Prod.fst := by
    rw [census592]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert592) 180 512
    2 AffineBoundaryCached.sheets592 AffineBoundaryCached.shadows592
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt592
    (AffineBoundaryCached.checked592) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census593 : (AffineBoundaryCached.cert593).seeds.map Prod.fst = AffineSearchData.allowed593 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 593 is a boundary. -/
theorem boundary593 : TopFiberBoundary 0x3804000800000002400bc0000098020004004000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3804000800000002400bc0000098020004004000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete593 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert593).beta ∈
      (AffineBoundaryCached.cert593).seeds.map Prod.fst := by
    rw [census593]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert593) 180 512
    2 AffineBoundaryCached.sheets593 AffineBoundaryCached.shadows593
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt593
    (AffineBoundaryCached.checked593) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census594 : (AffineBoundaryCached.cert594).seeds.map Prod.fst = AffineSearchData.allowed594 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 594 is a boundary. -/
theorem boundary594 : TopFiberBoundary 0x38040008000000030c09000000c002000400400001b := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38040008000000030c09000000c002000400400001b)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete594 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert594).beta ∈
      (AffineBoundaryCached.cert594).seeds.map Prod.fst := by
    rw [census594]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert594) 180 512
    2 AffineBoundaryCached.sheets594 AffineBoundaryCached.shadows594
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt594
    (AffineBoundaryCached.checked594) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census595 : (AffineBoundaryCached.cert595).seeds.map Prod.fst = AffineSearchData.allowed595 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 595 is a boundary. -/
theorem boundary595 : TopFiberBoundary 0x38040008000000048007c0000118020004004000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x38040008000000048007c0000118020004004000018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete595 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert595).beta ∈
      (AffineBoundaryCached.cert595).seeds.map Prod.fst := by
    rw [census595]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert595) 180 512
    2 AffineBoundaryCached.sheets595 AffineBoundaryCached.shadows595
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt595
    (AffineBoundaryCached.checked595) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census596 : (AffineBoundaryCached.cert596).seeds.map Prod.fst = AffineSearchData.allowed596 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 596 is a boundary. -/
theorem boundary596 : TopFiberBoundary 0x3805200a00000000000fc0000018010004005000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3805200a00000000000fc0000018010004005000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete596 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert596).beta ∈
      (AffineBoundaryCached.cert596).seeds.map Prod.fst := by
    rw [census596]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert596) 180 512
    2 AffineBoundaryCached.sheets596 AffineBoundaryCached.shadows596
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt596
    (AffineBoundaryCached.checked596) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census597 : (AffineBoundaryCached.cert597).seeds.map Prod.fst = AffineSearchData.allowed597 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 597 is a boundary. -/
theorem boundary597 : TopFiberBoundary 0x3806400c00000000000fc0000018008004006000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3806400c00000000000fc0000018008004006000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete597 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert597).beta ∈
      (AffineBoundaryCached.cert597).seeds.map Prod.fst := by
    rw [census597]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert597) 180 512
    4 AffineBoundaryCached.sheets597 AffineBoundaryCached.shadows597
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt597
    (AffineBoundaryCached.checked597) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census598 : (AffineBoundaryCached.cert598).seeds.map Prod.fst = AffineSearchData.allowed598 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 598 is a boundary. -/
theorem boundary598 : TopFiberBoundary 0x39c01008e0000020000004000018003000800000900 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x39c01008e0000020000004000018003000800000900)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete598 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert598).beta ∈
      (AffineBoundaryCached.cert598).seeds.map Prod.fst := by
    rw [census598]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert598) 180 512
    4 AffineBoundaryCached.sheets598 AffineBoundaryCached.shadows598
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt598
    (AffineBoundaryCached.checked598) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census599 : (AffineBoundaryCached.cert599).seeds.map Prod.fst = AffineSearchData.allowed599 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 599 is a boundary. -/
theorem boundary599 : TopFiberBoundary 0x3c02800400000000900a40140010000006002000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x3c02800400000000900a40140010000006002000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete599 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert599).beta ∈
      (AffineBoundaryCached.cert599).seeds.map Prod.fst := by
    rw [census599]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert599) 180 512
    4 AffineBoundaryCached.sheets599 AffineBoundaryCached.shadows599
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt599
    (AffineBoundaryCached.checked599) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census600 : (AffineBoundaryCached.cert600).seeds.map Prod.fst = AffineSearchData.allowed600 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 600 is a boundary. -/
theorem boundary600 : TopFiberBoundary 0x47c04400a0020000000000000018006004800c00100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x47c04400a0020000000000000018006004800c00100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete600 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert600).beta ∈
      (AffineBoundaryCached.cert600).seeds.map Prod.fst := by
    rw [census600]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert600) 180 512
    2 AffineBoundaryCached.sheets600 AffineBoundaryCached.shadows600
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt600
    (AffineBoundaryCached.checked600) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census601 : (AffineBoundaryCached.cert601).seeds.map Prod.fst = AffineSearchData.allowed601 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 601 is a boundary. -/
theorem boundary601 : TopFiberBoundary 0x4800920020000000fc01c0000020000604000100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x4800920020000000fc01c0000020000604000100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete601 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert601).beta ∈
      (AffineBoundaryCached.cert601).seeds.map Prod.fst := by
    rw [census601]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert601) 180 512
    8 AffineBoundaryCached.sheets601 AffineBoundaryCached.shadows601
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt601
    (AffineBoundaryCached.checked601) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census602 : (AffineBoundaryCached.cert602).seeds.map Prod.fst = AffineSearchData.allowed602 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 602 is a boundary. -/
theorem boundary602 : TopFiberBoundary 0x5000000000021a04a00b408000000280000000e8000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x5000000000021a04a00b408000000280000000e8000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete602 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert602).beta ∈
      (AffineBoundaryCached.cert602).seeds.map Prod.fst := by
    rw [census602]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert602) 180 512
    8 AffineBoundaryCached.sheets602 AffineBoundaryCached.shadows602
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt602
    (AffineBoundaryCached.checked602) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census603 : (AffineBoundaryCached.cert603).seeds.map Prod.fst = AffineSearchData.allowed603 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 603 is a boundary. -/
theorem boundary603 : TopFiberBoundary 0x7000000000000240200f80008008038000000006006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7000000000000240200f80008008038000000006006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete603 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert603).beta ∈
      (AffineBoundaryCached.cert603).seeds.map Prod.fst := by
    rw [census603]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert603) 180 512
    6 AffineBoundaryCached.sheets603 AffineBoundaryCached.shadows603
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt603
    (AffineBoundaryCached.checked603) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty

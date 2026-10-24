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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryCachedPart6
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty
open F2Mask FiberData

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census604 : (AffineBoundaryCached.cert604).seeds.map Prod.fst = AffineSearchData.allowed604 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 604 is a boundary. -/
theorem boundary604 : TopFiberBoundary 0x7001200200000048008fc0001000008000001000c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7001200200000048008fc0001000008000001000c00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete604 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert604).beta ∈
      (AffineBoundaryCached.cert604).seeds.map Prod.fst := by
    rw [census604]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert604) 180 512
    8 AffineBoundaryCached.sheets604 AffineBoundaryCached.shadows604
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt604
    (AffineBoundaryCached.checked604) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census605 : (AffineBoundaryCached.cert605).seeds.map Prod.fst = AffineSearchData.allowed605 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 605 is a boundary. -/
theorem boundary605 : TopFiberBoundary 0x7001200200000240040fc0008000008000001006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7001200200000240040fc0008000008000001006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete605 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert605).beta ∈
      (AffineBoundaryCached.cert605).seeds.map Prod.fst := by
    rw [census605]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert605) 180 512
    8 AffineBoundaryCached.sheets605 AffineBoundaryCached.shadows605
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt605
    (AffineBoundaryCached.checked605) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census606 : (AffineBoundaryCached.cert606).seeds.map Prod.fst = AffineSearchData.allowed606 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 606 is a boundary. -/
theorem boundary606 : TopFiberBoundary 0x7001200200001200200fc0040000008000001030000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7001200200001200200fc0040000008000001030000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete606 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert606).beta ∈
      (AffineBoundaryCached.cert606).seeds.map Prod.fst := by
    rw [census606]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert606) 180 512
    16 AffineBoundaryCached.sheets606 AffineBoundaryCached.shadows606
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt606
    (AffineBoundaryCached.checked606) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census607 : (AffineBoundaryCached.cert607).seeds.map Prod.fst = AffineSearchData.allowed607 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 607 is a boundary. -/
theorem boundary607 : TopFiberBoundary 0x7002400400000048008fc0001000010000002000c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7002400400000048008fc0001000010000002000c00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete607 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert607).beta ∈
      (AffineBoundaryCached.cert607).seeds.map Prod.fst := by
    rw [census607]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert607) 180 512
    8 AffineBoundaryCached.sheets607 AffineBoundaryCached.shadows607
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt607
    (AffineBoundaryCached.checked607) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census608 : (AffineBoundaryCached.cert608).seeds.map Prod.fst = AffineSearchData.allowed608 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 608 is a boundary. -/
theorem boundary608 : TopFiberBoundary 0x7002400400000240040fc0008000010000002006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7002400400000240040fc0008000010000002006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete608 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert608).beta ∈
      (AffineBoundaryCached.cert608).seeds.map Prod.fst := by
    rw [census608]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert608) 180 512
    8 AffineBoundaryCached.sheets608 AffineBoundaryCached.shadows608
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt608
    (AffineBoundaryCached.checked608) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census609 : (AffineBoundaryCached.cert609).seeds.map Prod.fst = AffineSearchData.allowed609 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 609 is a boundary. -/
theorem boundary609 : TopFiberBoundary 0x7004800800000048008fc0001000020000004000c00 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7004800800000048008fc0001000020000004000c00)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete609 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert609).beta ∈
      (AffineBoundaryCached.cert609).seeds.map Prod.fst := by
    rw [census609]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert609) 180 512
    8 AffineBoundaryCached.sheets609 AffineBoundaryCached.shadows609
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt609
    (AffineBoundaryCached.checked609) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census610 : (AffineBoundaryCached.cert610).seeds.map Prod.fst = AffineSearchData.allowed610 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 610 is a boundary. -/
theorem boundary610 : TopFiberBoundary 0x7004800800000240040fc0008000020000004006000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7004800800000240040fc0008000020000004006000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete610 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert610).beta ∈
      (AffineBoundaryCached.cert610).seeds.map Prod.fst := by
    rw [census610]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert610) 180 512
    8 AffineBoundaryCached.sheets610 AffineBoundaryCached.shadows610
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt610
    (AffineBoundaryCached.checked610) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census611 : (AffineBoundaryCached.cert611).seeds.map Prod.fst = AffineSearchData.allowed611 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 611 is a boundary. -/
theorem boundary611 : TopFiberBoundary 0x700b401400000000000fc000000019000000a000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x700b401400000000000fc000000019000000a000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete611 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert611).beta ∈
      (AffineBoundaryCached.cert611).seeds.map Prod.fst := by
    rw [census611]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert611) 180 512
    8 AffineBoundaryCached.sheets611 AffineBoundaryCached.shadows611
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt611
    (AffineBoundaryCached.checked611) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census612 : (AffineBoundaryCached.cert612).seeds.map Prod.fst = AffineSearchData.allowed612 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 612 is a boundary. -/
theorem boundary612 : TopFiberBoundary 0x700d801800000000000fc00000001a000000c000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x700d801800000000000fc00000001a000000c000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete612 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert612).beta ∈
      (AffineBoundaryCached.cert612).seeds.map Prod.fst := by
    rw [census612]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert612) 180 512
    8 AffineBoundaryCached.sheets612 AffineBoundaryCached.shadows612
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt612
    (AffineBoundaryCached.checked612) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census613 : (AffineBoundaryCached.cert613).seeds.map Prod.fst = AffineSearchData.allowed613 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 613 is a boundary. -/
theorem boundary613 : TopFiberBoundary 0x7049208200000000000fc0000000c08000041000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7049208200000000000fc0000000c08000041000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete613 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert613).beta ∈
      (AffineBoundaryCached.cert613).seeds.map Prod.fst := by
    rw [census613]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert613) 180 512
    8 AffineBoundaryCached.sheets613 AffineBoundaryCached.shadows613
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt613
    (AffineBoundaryCached.checked613) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census614 : (AffineBoundaryCached.cert614).seeds.map Prod.fst = AffineSearchData.allowed614 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 614 is a boundary. -/
theorem boundary614 : TopFiberBoundary 0x704a408400000000000fc0000000c10000042000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x704a408400000000000fc0000000c10000042000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete614 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert614).beta ∈
      (AffineBoundaryCached.cert614).seeds.map Prod.fst := by
    rw [census614]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert614) 180 512
    8 AffineBoundaryCached.sheets614 AffineBoundaryCached.shadows614
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt614
    (AffineBoundaryCached.checked614) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census615 : (AffineBoundaryCached.cert615).seeds.map Prod.fst = AffineSearchData.allowed615 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 615 is a boundary. -/
theorem boundary615 : TopFiberBoundary 0x704c808800000000000fc0000000c20000044000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x704c808800000000000fc0000000c20000044000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete615 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert615).beta ∈
      (AffineBoundaryCached.cert615).seeds.map Prod.fst := by
    rw [census615]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert615) 180 512
    8 AffineBoundaryCached.sheets615 AffineBoundaryCached.shadows615
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt615
    (AffineBoundaryCached.checked615) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census616 : (AffineBoundaryCached.cert616).seeds.map Prod.fst = AffineSearchData.allowed616 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 616 is a boundary. -/
theorem boundary616 : TopFiberBoundary 0x7201000200000000fc0c40180008000001001000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7201000200000000fc0c40180008000001001000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete616 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert616).beta ∈
      (AffineBoundaryCached.cert616).seeds.map Prod.fst := by
    rw [census616]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert616) 180 512
    4 AffineBoundaryCached.sheets616 AffineBoundaryCached.shadows616
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt616
    (AffineBoundaryCached.checked616) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census617 : (AffineBoundaryCached.cert617).seeds.map Prod.fst = AffineSearchData.allowed617 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 617 is a boundary. -/
theorem boundary617 : TopFiberBoundary 0x7241240200000000000fc0000006008000201000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7241240200000000000fc0000006008000201000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete617 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert617).beta ∈
      (AffineBoundaryCached.cert617).seeds.map Prod.fst := by
    rw [census617]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert617) 180 512
    8 AffineBoundaryCached.sheets617 AffineBoundaryCached.shadows617
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt617
    (AffineBoundaryCached.checked617) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census618 : (AffineBoundaryCached.cert618).seeds.map Prod.fst = AffineSearchData.allowed618 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 618 is a boundary. -/
theorem boundary618 : TopFiberBoundary 0x7242440400000000000fc0000006010000202000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7242440400000000000fc0000006010000202000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete618 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert618).beta ∈
      (AffineBoundaryCached.cert618).seeds.map Prod.fst := by
    rw [census618]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert618) 180 512
    8 AffineBoundaryCached.sheets618 AffineBoundaryCached.shadows618
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt618
    (AffineBoundaryCached.checked618) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census619 : (AffineBoundaryCached.cert619).seeds.map Prod.fst = AffineSearchData.allowed619 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 619 is a boundary. -/
theorem boundary619 : TopFiberBoundary 0x7244840800000000000fc0000006020000204000000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7244840800000000000fc0000006020000204000000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete619 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert619).beta ∈
      (AffineBoundaryCached.cert619).seeds.map Prod.fst := by
    rw [census619]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert619) 180 512
    8 AffineBoundaryCached.sheets619 AffineBoundaryCached.shadows619
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt619
    (AffineBoundaryCached.checked619) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census620 : (AffineBoundaryCached.cert620).seeds.map Prod.fst = AffineSearchData.allowed620 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 620 is a boundary. -/
theorem boundary620 : TopFiberBoundary 0x7400400000001200040b00100020028002000030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7400400000001200040b00100020028002000030006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete620 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert620).beta ∈
      (AffineBoundaryCached.cert620).seeds.map Prod.fst := by
    rw [census620]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert620) 180 512
    8 AffineBoundaryCached.sheets620 AffineBoundaryCached.shadows620
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt620
    (AffineBoundaryCached.checked620) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census621 : (AffineBoundaryCached.cert621).seeds.map Prod.fst = AffineSearchData.allowed621 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 621 is a boundary. -/
theorem boundary621 : TopFiberBoundary 0x7402000400001200040b00100020000002002030006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x7402000400001200040b00100020000002002030006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete621 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert621).beta ∈
      (AffineBoundaryCached.cert621).seeds.map Prod.fst := by
    rw [census621]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert621) 180 512
    4 AffineBoundaryCached.sheets621 AffineBoundaryCached.shadows621
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt621
    (AffineBoundaryCached.checked621) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census622 : (AffineBoundaryCached.cert622).seeds.map Prod.fst = AffineSearchData.allowed622 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 622 is a boundary. -/
theorem boundary622 : TopFiberBoundary 0x8000000090002018202000800640040000a00140070 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8000000090002018202000800640040000a00140070)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete622 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert622).beta ∈
      (AffineBoundaryCached.cert622).seeds.map Prod.fst := by
    rw [census622]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert622) 180 512
    4 AffineBoundaryCached.sheets622 AffineBoundaryCached.shadows622
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt622
    (AffineBoundaryCached.checked622) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census623 : (AffineBoundaryCached.cert623).seeds.map Prod.fst = AffineSearchData.allowed623 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 623 is a boundary. -/
theorem boundary623 : TopFiberBoundary 0x8000048008012019002200800600040c000001000c0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8000048008012019002200800600040c000001000c0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete623 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert623).beta ∈
      (AffineBoundaryCached.cert623).seeds.map Prod.fst := by
    rw [census623]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert623) 180 512
    8 AffineBoundaryCached.sheets623 AffineBoundaryCached.shadows623
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt623
    (AffineBoundaryCached.checked623) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census624 : (AffineBoundaryCached.cert624).seeds.map Prod.fst = AffineSearchData.allowed624 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 624 is a boundary. -/
theorem boundary624 : TopFiberBoundary 0x80001200200120190022008006000406000000400c0 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x80001200200120190022008006000406000000400c0)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete624 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert624).beta ∈
      (AffineBoundaryCached.cert624).seeds.map Prod.fst := by
    rw [census624]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert624) 180 512
    8 AffineBoundaryCached.sheets624 AffineBoundaryCached.shadows624
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt624
    (AffineBoundaryCached.checked624) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census625 : (AffineBoundaryCached.cert625).seeds.map Prod.fst = AffineSearchData.allowed625 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 625 is a boundary. -/
theorem boundary625 : TopFiberBoundary 0x800012019000600f000200000200040600c00080000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x800012019000600f000200000200040600c00080000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete625 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert625).beta ∈
      (AffineBoundaryCached.cert625).seeds.map Prod.fst := by
    rw [census625]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert625) 180 512
    4 AffineBoundaryCached.sheets625 AffineBoundaryCached.shadows625
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt625
    (AffineBoundaryCached.checked625) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census626 : (AffineBoundaryCached.cert626).seeds.map Prod.fst = AffineSearchData.allowed626 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 626 is a boundary. -/
theorem boundary626 : TopFiberBoundary 0x80010000000024002c0280100198008008000028003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x80010000000024002c0280100198008008000028003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete626 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert626).beta ∈
      (AffineBoundaryCached.cert626).seeds.map Prod.fst := by
    rw [census626]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert626) 180 512
    8 AffineBoundaryCached.sheets626 AffineBoundaryCached.shadows626
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt626
    (AffineBoundaryCached.checked626) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census627 : (AffineBoundaryCached.cert627).seeds.map Prod.fst = AffineSearchData.allowed627 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 627 is a boundary. -/
theorem boundary627 : TopFiberBoundary 0x8004a00a00002400400240100180020008005028000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8004a00a00002400400240100180020008005028000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete627 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert627).beta ∈
      (AffineBoundaryCached.cert627).seeds.map Prod.fst := by
    rw [census627]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert627) 180 512
    8 AffineBoundaryCached.sheets627 AffineBoundaryCached.shadows627
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt627
    (AffineBoundaryCached.checked627) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census628 : (AffineBoundaryCached.cert628).seeds.map Prod.fst = AffineSearchData.allowed628 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 628 is a boundary. -/
theorem boundary628 : TopFiberBoundary 0x8004a00a00004800800240080180020008005018000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8004a00a00004800800240080180020008005018000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete628 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert628).beta ∈
      (AffineBoundaryCached.cert628).seeds.map Prod.fst := by
    rw [census628]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert628) 180 512
    8 AffineBoundaryCached.sheets628 AffineBoundaryCached.shadows628
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt628
    (AffineBoundaryCached.checked628) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census629 : (AffineBoundaryCached.cert629).seeds.map Prod.fst = AffineSearchData.allowed629 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 629 is a boundary. -/
theorem boundary629 : TopFiberBoundary 0x800800004800801b00a006000a00200040c00000080 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x800800004800801b00a006000a00200040c00000080)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete629 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert629).beta ∈
      (AffineBoundaryCached.cert629).seeds.map Prod.fst := by
    rw [census629]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert629) 180 512
    8 AffineBoundaryCached.sheets629 AffineBoundaryCached.shadows629
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt629
    (AffineBoundaryCached.checked629) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census630 : (AffineBoundaryCached.cert630).seeds.map Prod.fst = AffineSearchData.allowed630 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 630 is a boundary. -/
theorem boundary630 : TopFiberBoundary 0x800800009001001b00a006000a00200040a00000040 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x800800009001001b00a006000a00200040a00000040)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete630 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert630).beta ∈
      (AffineBoundaryCached.cert630).seeds.map Prod.fst := by
    rw [census630]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert630) 180 512
    8 AffineBoundaryCached.sheets630 AffineBoundaryCached.shadows630
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt630
    (AffineBoundaryCached.checked630) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census631 : (AffineBoundaryCached.cert631).seeds.map Prod.fst = AffineSearchData.allowed631 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 631 is a boundary. -/
theorem boundary631 : TopFiberBoundary 0x8104104020012002001200800000680600120040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8104104020012002001200800000680600120040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete631 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert631).beta ∈
      (AffineBoundaryCached.cert631).seeds.map Prod.fst := by
    rw [census631]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert631) 180 512
    10 AffineBoundaryCached.sheets631 AffineBoundaryCached.shadows631
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt631
    (AffineBoundaryCached.checked631) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census632 : (AffineBoundaryCached.cert632).seeds.map Prod.fst = AffineSearchData.allowed632 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 632 is a boundary. -/
theorem boundary632 : TopFiberBoundary 0x8160060008000000009006000c00800c40140040000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8160060008000000009006000c00800c40140040000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete632 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert632).beta ∈
      (AffineBoundaryCached.cert632).seeds.map Prod.fst := by
    rw [census632]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert632) 180 512
    8 AffineBoundaryCached.sheets632 AffineBoundaryCached.shadows632
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt632
    (AffineBoundaryCached.checked632) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census633 : (AffineBoundaryCached.cert633).seeds.map Prod.fst = AffineSearchData.allowed633 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 633 is a boundary. -/
theorem boundary633 : TopFiberBoundary 0x8160108020000000009006000c00800640140100000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8160108020000000009006000c00800640140100000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete633 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert633).beta ∈
      (AffineBoundaryCached.cert633).seeds.map Prod.fst := by
    rw [census633]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert633) 180 512
    8 AffineBoundaryCached.sheets633 AffineBoundaryCached.shadows633
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt633
    (AffineBoundaryCached.checked633) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census634 : (AffineBoundaryCached.cert634).seeds.map Prod.fst = AffineSearchData.allowed634 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 634 is a boundary. -/
theorem boundary634 : TopFiberBoundary 0x8201200000000002bc05c0000108000009000000028 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8201200000000002bc05c0000108000009000000028)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete634 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert634).beta ∈
      (AffineBoundaryCached.cert634).seeds.map Prod.fst := by
    rw [census634]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert634) 180 512
    4 AffineBoundaryCached.sheets634 AffineBoundaryCached.shadows634
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt634
    (AffineBoundaryCached.checked634) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census635 : (AffineBoundaryCached.cert635).seeds.map Prod.fst = AffineSearchData.allowed635 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 635 is a boundary. -/
theorem boundary635 : TopFiberBoundary 0x82012000000000047c09c0000088000009000000018 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x82012000000000047c09c0000088000009000000018)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete635 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert635).beta ∈
      (AffineBoundaryCached.cert635).seeds.map Prod.fst := by
    rw [census635]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert635) 180 512
    4 AffineBoundaryCached.sheets635 AffineBoundaryCached.shadows635
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt635
    (AffineBoundaryCached.checked635) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census636 : (AffineBoundaryCached.cert636).seeds.map Prod.fst = AffineSearchData.allowed636 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 636 is a boundary. -/
theorem boundary636 : TopFiberBoundary 0x82012000000000063c0dc0000008000009000000030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x82012000000000063c0dc0000008000009000000030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete636 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert636).beta ∈
      (AffineBoundaryCached.cert636).seeds.map Prod.fst := by
    rw [census636]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert636) 180 512
    4 AffineBoundaryCached.sheets636 AffineBoundaryCached.shadows636
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt636
    (AffineBoundaryCached.checked636) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census637 : (AffineBoundaryCached.cert637).seeds.map Prod.fst = AffineSearchData.allowed637 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 637 is a boundary. -/
theorem boundary637 : TopFiberBoundary 0x8201200000000007380f80000040000009000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8201200000000007380f80000040000009000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete637 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert637).beta ∈
      (AffineBoundaryCached.cert637).seeds.map Prod.fst := by
    rw [census637]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert637) 180 512
    4 AffineBoundaryCached.sheets637 AffineBoundaryCached.shadows637
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt637
    (AffineBoundaryCached.checked637) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census638 : (AffineBoundaryCached.cert638).seeds.map Prod.fst = AffineSearchData.allowed638 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 638 is a boundary. -/
theorem boundary638 : TopFiberBoundary 0x8201200000000007700f00000050000009000000003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8201200000000007700f00000050000009000000003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete638 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert638).beta ∈
      (AffineBoundaryCached.cert638).seeds.map Prod.fst := by
    rw [census638]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert638) 180 512
    4 AffineBoundaryCached.sheets638 AffineBoundaryCached.shadows638
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt638
    (AffineBoundaryCached.checked638) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census639 : (AffineBoundaryCached.cert639).seeds.map Prod.fst = AffineSearchData.allowed639 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 639 is a boundary. -/
theorem boundary639 : TopFiberBoundary 0x8201200000000007a80e80000060000009000000005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8201200000000007a80e80000060000009000000005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete639 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert639).beta ∈
      (AffineBoundaryCached.cert639).seeds.map Prod.fst := by
    rw [census639]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert639) 180 512
    4 AffineBoundaryCached.sheets639 AffineBoundaryCached.shadows639
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt639
    (AffineBoundaryCached.checked639) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census640 : (AffineBoundaryCached.cert640).seeds.map Prod.fst = AffineSearchData.allowed640 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 640 is a boundary. -/
theorem boundary640 : TopFiberBoundary 0x860040004004000000048014019802000d001000200 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x860040004004000000048014019802000d001000200)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete640 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert640).beta ∈
      (AffineBoundaryCached.cert640).seeds.map Prod.fst := by
    rw [census640]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert640) 180 512
    2 AffineBoundaryCached.sheets640 AffineBoundaryCached.shadows640
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt640
    (AffineBoundaryCached.checked640) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census641 : (AffineBoundaryCached.cert641).seeds.map Prod.fst = AffineSearchData.allowed641 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 641 is a boundary. -/
theorem boundary641 : TopFiberBoundary 0x8801800000000000240b0014019002800c000000006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x8801800000000000240b0014019002800c000000006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete641 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert641).beta ∈
      (AffineBoundaryCached.cert641).seeds.map Prod.fst := by
    rw [census641]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert641) 180 512
    8 AffineBoundaryCached.sheets641 AffineBoundaryCached.shadows641
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt641
    (AffineBoundaryCached.checked641) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census642 : (AffineBoundaryCached.cert642).seeds.map Prod.fst = AffineSearchData.allowed642 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 642 is a boundary. -/
theorem boundary642 : TopFiberBoundary 0x90010048200048024004000001000000100d800400c := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x90010048200048024004000001000000100d800400c)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete642 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert642).beta ∈
      (AffineBoundaryCached.cert642).seeds.map Prod.fst := by
    rw [census642]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert642) 180 512
    10 AffineBoundaryCached.sheets642 AffineBoundaryCached.shadows642
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt642
    (AffineBoundaryCached.checked642) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census643 : (AffineBoundaryCached.cert643).seeds.map Prod.fst = AffineSearchData.allowed643 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 643 is a boundary. -/
theorem boundary643 : TopFiberBoundary 0xb000200200004806400880040000020008001018030 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xb000200200004806400880040000020008001018030)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete643 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert643).beta ∈
      (AffineBoundaryCached.cert643).seeds.map Prod.fst := by
    rw [census643]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert643) 180 512
    4 AffineBoundaryCached.sheets643 AffineBoundaryCached.shadows643
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt643
    (AffineBoundaryCached.checked643) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census644 : (AffineBoundaryCached.cert644).seeds.map Prod.fst = AffineSearchData.allowed644 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 644 is a boundary. -/
theorem boundary644 : TopFiberBoundary 0x10001600280080000000480140140008015003000400 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x10001600280080000000480140140008015003000400)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete644 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert644).beta ∈
      (AffineBoundaryCached.cert644).seeds.map Prod.fst := by
    rw [census644]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert644) 180 512
    8 AffineBoundaryCached.sheets644 AffineBoundaryCached.shadows644
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt644
    (AffineBoundaryCached.checked644) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census645 : (AffineBoundaryCached.cert645).seeds.map Prod.fst = AffineSearchData.allowed645 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 645 is a boundary. -/
theorem boundary645 : TopFiberBoundary 0x20e006001001000000006c00c00c0000024004000800 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x20e006001001000000006c00c00c0000024004000800)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete645 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert645).beta ∈
      (AffineBoundaryCached.cert645).seeds.map Prod.fst := by
    rw [census645]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert645) 180 512
    2 AffineBoundaryCached.sheets645 AffineBoundaryCached.shadows645
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt645
    (AffineBoundaryCached.checked645) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census646 : (AffineBoundaryCached.cert646).seeds.map Prod.fst = AffineSearchData.allowed646 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 646 is a boundary. -/
theorem boundary646 : TopFiberBoundary 0x40820120090010009008006000203400000300000100 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x40820120090010009008006000203400000300000100)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete646 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert646).beta ∈
      (AffineBoundaryCached.cert646).seeds.map Prod.fst := by
    rw [census646]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert646) 180 512
    10 AffineBoundaryCached.sheets646 AffineBoundaryCached.shadows646
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt646
    (AffineBoundaryCached.checked646) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census647 : (AffineBoundaryCached.cert647).seeds.map Prod.fst = AffineSearchData.allowed647 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 647 is a boundary. -/
theorem boundary647 : TopFiberBoundary 0x41009024020004002400400000d000000880c0020008 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x41009024020004002400400000d000000880c0020008)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete647 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert647).beta ∈
      (AffineBoundaryCached.cert647).seeds.map Prod.fst := by
    rw [census647]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert647) 180 512
    10 AffineBoundaryCached.sheets647 AffineBoundaryCached.shadows647
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt647
    (AffineBoundaryCached.checked647) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census648 : (AffineBoundaryCached.cert648).seeds.map Prod.fst = AffineSearchData.allowed648 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 648 is a boundary. -/
theorem boundary648 : TopFiberBoundary 0x200200001201000940140040018000001030030004001 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200001201000940140040018000001030030004001)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete648 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert648).beta ∈
      (AffineBoundaryCached.cert648).seeds.map Prod.fst := by
    rw [census648]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert648) 180 512
    8 AffineBoundaryCached.sheets648 AffineBoundaryCached.shadows648
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt648
    (AffineBoundaryCached.checked648) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census649 : (AffineBoundaryCached.cert649).seeds.map Prod.fst = AffineSearchData.allowed649 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 649 is a boundary. -/
theorem boundary649 : TopFiberBoundary 0x200200009001000fc01c0040008000001180000008000 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0x200200009001000fc01c0040008000001180000008000)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete649 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert649).beta ∈
      (AffineBoundaryCached.cert649).seeds.map Prod.fst := by
    rw [census649]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert649) 180 512
    8 AffineBoundaryCached.sheets649 AffineBoundaryCached.shadows649
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt649
    (AffineBoundaryCached.checked649) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census650 : (AffineBoundaryCached.cert650).seeds.map Prod.fst = AffineSearchData.allowed650 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 650 is a boundary. -/
theorem boundary650 : TopFiberBoundary 0xfc01c0048008000000240040000008000200000040006 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0048008000000240040000008000200000040006)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete650 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert650).beta ∈
      (AffineBoundaryCached.cert650).seeds.map Prod.fst := by
    rw [census650]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert650) 180 512
    8 AffineBoundaryCached.sheets650 AffineBoundaryCached.shadows650
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt650
    (AffineBoundaryCached.checked650) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census651 : (AffineBoundaryCached.cert651).seeds.map Prod.fst = AffineSearchData.allowed651 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 651 is a boundary. -/
theorem boundary651 : TopFiberBoundary 0xfc01c0090010000000480080000010000400000080005 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0090010000000480080000010000400000080005)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete651 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert651).beta ∈
      (AffineBoundaryCached.cert651).seeds.map Prod.fst := by
    rw [census651]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert651) 180 512
    8 AffineBoundaryCached.sheets651 AffineBoundaryCached.shadows651
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt651
    (AffineBoundaryCached.checked651) hw he hseed

/-- The affine witness and search certificates use the same outside-support census. -/
theorem census652 : (AffineBoundaryCached.cert652).seeds.map Prod.fst = AffineSearchData.allowed652 := by decide +kernel

/-- Every short top lift in nonempty affine fiber 652 is a boundary. -/
theorem boundary652 : TopFiberBoundary 0xfc01c0120020000000900100000020000800000100003 := by
  intro word hw he hweight
  have hcap : (22-bitCount 180 0xfc01c0120020000000900100000020000800000100003)/2 = 1 := by decide +kernel
  rw [hcap] at hweight
  have hoff := AffineSearchData.complete652 hw he hweight
  have hseed : outsideMask word (AffineBoundaryCached.cert652).beta ∈
      (AffineBoundaryCached.cert652).seeds.map Prod.fst := by
    rw [census652]
    exact hoff
  exact AffineMaskCertificate.indexedBoundary_of_check (AffineBoundaryCached.cert652) 180 512
    8 AffineBoundaryCached.sheets652 AffineBoundaryCached.shadows652
    topEColumns topRColumns boundaryColumns topJoin AffineBoundaryCached.boundaryAt652
    (AffineBoundaryCached.checked652) hw he hseed

end Quantum.Stabilizer.Homological.BB.Bravyi360.TopNonempty

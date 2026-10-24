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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineColumnCache
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialPart5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineBoundaryGroup5
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.FiberData

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.AffineBoundaryCached
open F2Mask PackedDigits AffineBoundaryGroups.Group5

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 504. -/
noncomputable def sheets504 : Nat := 0x58000008000048000009000400180200040000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400400000000000080024000000001000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000800800004800000900040000020000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008048000000000008002400000180100040040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180000080000480000000008001800000400001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000800b400c00000300000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100400000000480000090004000003800000401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000800000000800240000018008004000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows504 : Nat := 0x1804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b4004001803000400401800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001804000800004800800b40040018030004004018000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices504 : sheets504 = boundedSlice 512 0 8 sheetTable ∧
    shadows504 = boundedSlice 512 0 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt504 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets504) (lane 512 i shadows504) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 0 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices504.1 slices504.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 504. -/
noncomputable def cert504 : AffineMaskCertificate := {
 beta := 0x1804000800004800800b40040018030004004018000
 sectionColumns := [(34,0x4800000000000000000000000018000),(58,0x800000000000000000000000000000),(63,0x8000),(64,0x4000000000000000000000000008000),(83,0x4000000),(101,0x900000000020004000000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(130,0x4000800000000000200000000010000004000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x4000000000000000200000000000000004000000),(137,0x800000000000000000000000),(153,0x40040008000000000000000),(154,0x800000000000000000940040008020004000000000),(159,0x40000000000000000000),(160,0x804000800000000000b40040018030004004000000),(161,0x4800800000000000000000000018000)]
 kernelColumns := [(0,0x1804000800004800800b40040018030004004018000)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x80000000000000000000,[2,3]),(0x800000000000000000000000000000000000000,[4,5]),(0x4000000000000000000000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked504 : (cert504).checkIndexedBoundary 180 512 8 sheets504 shadows504 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x3f0000006c0000d800000240000240006c0000db6 = reconX FiberData.topRColumns (cert504).beta := AffineSearchData.rhsChecked504.symm
  have h : (cert504).checkIndexedBoundaryCached 180 512 8 sheets504 shadows504 0x3f0000006c0000d800000240000240006c0000db6 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 505. -/
noncomputable def sheets505 : Nat := 0x180120080000000024000018001000000400100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000200000000000b000c0000000000004000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows505 : Nat := 0x1805200a00000000240b0014001000000400500000600000000000000000000000000000000000000000000000000000000000000000000000000000000000001805200a00000000240b00140010000004005000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices505 : sheets505 = boundedSlice 512 8 2 sheetTable ∧
    shadows505 = boundedSlice 512 8 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt505 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets505) (lane 512 i shadows505) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 8 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices505.1 slices505.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 505. -/
noncomputable def cert505 : AffineMaskCertificate := {
 beta := 0x1805200a00000000240b00140010000004005000006
 sectionColumns := [(29,0x200000040000000000000000006),(34,0x2),(35,0x200000040000000000000000002),(77,0x5000000000000000a00000000000000005000000),(81,0x1000000),(83,0x5000000000000000a00000000000000001000000),(105,0x5000a00000000000a00000000000004005000000),(106,0x5000200000000000a00000000000004005000000),(107,0x5000000000000000a00000000000004005000000),(130,0x200000000000000100000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x1000000000000000800000000000000001000000),(137,0x800000000000000000000000),(153,0x240000040000000000000000006),(154,0x800000000000000240000040000000000000000006),(159,0x40000000000000000000),(160,0x800200000000000240100040010000000000000006),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x1805200a00000000240b00140010000004005000006)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked505 : (cert505).checkIndexedBoundary 180 512 2 sheets505 shadows505 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b000036900000d8000002400002d000db6000db6 = reconX FiberData.topRColumns (cert505).beta := AffineSearchData.rhsChecked505.symm
  have h : (cert505).checkIndexedBoundaryCached 180 512 2 sheets505 shadows505 0x1b000036900000d8000002400002d000db6000db6 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 506. -/
noncomputable def sheets506 : Nat := 0x120000000000000024008001800800400100000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000ca0058000004000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000000000000c001800000400100000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000ee001800000c000000000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows506 : Nat := 0x1a00200000000000ee00d801800c00400100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00200000000000ee00d801800c00400100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00200000000000ee00d801800c00400100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00200000000000ee00d801800c004001000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices506 : sheets506 = boundedSlice 512 10 4 sheetTable ∧
    shadows506 = boundedSlice 512 10 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt506 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets506) (lane 512 i shadows506) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 10 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices506.1 slices506.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 506. -/
noncomputable def cert506 : AffineMaskCertificate := {
 beta := 0x1a00200000000000ee00d801800c004001000000000
 sectionColumns := [(22,0xc0018018000000000000000000),(29,0x40008008000000000000000000),(35,0x200048008008000000000000000),(99,0xa002000000000000e0090010004004000000000000),(101,0x8000000000000000c0000000000000000000000000),(105,0xa002000000000000e0090010004004001000000000),(125,0x8002000000000000c0080000000004000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(149,0xe0018018000000000000000000),(153,0x8008000000000000000000),(154,0xc0008008000000000000000000),(155,0x800200000000000020098018004004000000000000),(159,0x48008008000000000000000),(160,0x600048008008000000000000000),(161,0x800000000000000000000000000),(177,0x8000000000000000000000),(178,0xc0008018000000000000000000)]
 kernelColumns := [(0,0x1a00200000000000ee00d801800c004001000000000)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1]),(0x4,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked506 : (cert506).checkIndexedBoundary 180 512 4 sheets506 shadows506 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x6c0036b40000fe4000024000009000000000492000012 = reconX FiberData.topRColumns (cert506).beta := AffineSearchData.rhsChecked506.symm
  have h : (cert506).checkIndexedBoundaryCached 180 512 4 sheets506 shadows506 0x6c0036b40000fe4000024000009000000000492000012 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 507. -/
noncomputable def sheets507 : Nat := 0x12008000000000000008c00c000002000100000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000fc0000000010000004000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows507 : Nat := 0x1a00a00000000000fc08c00c001002000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00a00000000000fc08c00c0010020005000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices507 : sheets507 = boundedSlice 512 14 2 sheetTable ∧
    shadows507 = boundedSlice 512 14 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt507 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets507) (lane 512 i shadows507) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 14 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices507.1 slices507.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 507. -/
noncomputable def cert507 : AffineMaskCertificate := {
 beta := 0x1a00a00000000000fc08c00c0010020005000000000
 sectionColumns := [(29,0x80080080010000000000000000),(34,0x6000000c0000000000000000000),(35,0x400000080000000000000000000),(75,0x800a000000000000c0840000000020004000000000),(77,0x8000000000000000c0000000000000000000000),(99,0x200000000000000100080080010000000000000000),(101,0x8000000000000000c0000000000000000000000000),(105,0xa00a000000000001c08c0080010020005000000000),(107,0x8008000000000000c00c0000000000004000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x8008000000000000c08c0000000020004000000000),(137,0x800000000000000000000000),(153,0xc0080080010000000000000000),(154,0x80080010000000000000000),(155,0x100000000000000000000000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0xe000000c0000000000000000000)]
 kernelColumns := [(0,0x1a00a00000000000fc08c00c0010020005000000000)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked507 : (cert507).checkIndexedBoundary 180 512 2 sheets507 shadows507 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x2dd8000090000090000002d000000000492000012 = reconX FiberData.topRColumns (cert507).beta := AffineSearchData.rhsChecked507.symm
  have h : (cert507).checkIndexedBoundaryCached 180 512 2 sheets507 shadows507 0x2dd8000090000090000002d000000000492000012 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 508. -/
noncomputable def sheets508 : Nat := 0x120080000000120000084008000002000100000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000940000000000000004000030003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows508 : Nat := 0x1a00a0000000120094084008000002000500003000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00a00000001200940840080000020005000030005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices508 : sheets508 = boundedSlice 512 16 2 sheetTable ∧
    shadows508 = boundedSlice 512 16 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt508 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets508) (lane 512 i shadows508) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 16 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices508.1 slices508.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 508. -/
noncomputable def cert508 : AffineMaskCertificate := {
 beta := 0x1a00a00000001200940840080000020005000030005
 sectionColumns := [(33,0x1),(34,0x1200000000000000000000000030004),(35,0x4),(59,0x200000000000000000000000000000),(64,0x1200000000000000000000000020004),(65,0x200000000000000000000000020004),(99,0xa00a00000000000140840000000020004000000000),(101,0xa00000000000000840000000020004000000000),(105,0xa00a00000000000140840000000020005000000000),(107,0xa00000000000000840000000020000000000000),(129,0x40000000000000000000000),(130,0x800000000000000040000000000000000000000),(131,0xa00000000000000040000000000000000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x800a00000000000040840000000020004000000000),(155,0x100000000000000000000000000),(160,0x80000000000000000000),(161,0x1200800000000000000000000030005)]
 kernelColumns := [(0,0x1a00a00000001200940840080000020005000030005)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked508 : (cert508).checkIndexedBoundary 180 512 2 sheets508 shadows508 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x24d80000d8000090000002d036d80000db600001b = reconX FiberData.topRColumns (cert508).beta := AffineSearchData.rhsChecked508.symm
  have h : (cert508).checkIndexedBoundaryCached 180 512 2 sheets508 shadows508 0x24d80000d8000090000002d036d80000db600001b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 509. -/
noncomputable def sheets509 : Nat := 0x12008002000000002408000c000801000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000801000000000000900040000008000004001000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000012008002000000000008400c000001000100000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000801000000000000b40000000000000004001000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows509 : Nat := 0x1a01800200000000b408400c000001000500100000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001a01800200000000b408400c000001000500100000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001a01800200000000b408400c000001000500100000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001a01800200000000b408400c0000010005001000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices509 : sheets509 = boundedSlice 512 18 4 sheetTable ∧
    shadows509 = boundedSlice 512 18 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt509 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets509) (lane 512 i shadows509) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 18 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices509.1 slices509.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 509. -/
noncomputable def cert509 : AffineMaskCertificate := {
 beta := 0x1a01800200000000b408400c0000010005001000005
 sectionColumns := [(33,0x1),(34,0x200000040000000000000000004),(35,0x4),(81,0x1000000),(99,0xa01800200000000140840000000010004001000000),(101,0x1800200000000000840000000010004001000000),(105,0xa01800200000000140840000000010005001000000),(106,0x1800000000000000840000000010000001000000),(107,0x1800200000000000840000000010000001000000),(129,0x40000000000000000000000),(130,0x800000000000000040000000000000000000000),(136,0x1000000000000000800000000000000001000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x801800200000000040840000000010004001000000),(155,0x100000000000000000000000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0xa00000040000000000000000005)]
 kernelColumns := [(0,0x1a01800200000000b408400c0000010005001000005)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1]),(0x8000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked509 : (cert509).checkIndexedBoundary 180 512 4 sheets509 shadows509 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x2dd8003600000090000002d000009000db600001b = reconX FiberData.topRColumns (cert509).beta := AffineSearchData.rhsChecked509.symm
  have h : (cert509).checkIndexedBoundaryCached 180 512 4 sheets509 shadows509 0x2dd8003600000090000002d000009000db600001b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 510. -/
noncomputable def sheets510 : Nat := 0x520640000000000000000000000001000100600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800200c000000000009000c002800000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200800c000000000009000c000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000806e00000000000000000000028010004006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012064000000000000009000c000003000100600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200c00000000000000000028020004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012040004000000000009000c000001800100400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000802600800000000000000000028008004002000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows510 : Nat := 0x1a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c002801000500600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a06600c000000000009000c0028010005006000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices510 : sheets510 = boundedSlice 512 22 8 sheetTable ∧
    shadows510 = boundedSlice 512 22 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt510 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets510) (lane 512 i shadows510) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 22 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices510.1 slices510.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 510. -/
noncomputable def cert510 : AffineMaskCertificate := {
 beta := 0x1a06600c000000000009000c0028010005006000000
 sectionColumns := [(82,0x2000000),(83,0x4000000),(99,0x6200800000000000900000000010001006000000),(101,0x6200c00000000000900000000010004006000000),(105,0x6200800000000000900000000010000006000000),(106,0x6200000000000000900000000010000006000000),(107,0x6200c00000000000900000000010000006000000),(129,0x400000000000000100000000000000000000000),(130,0x200000000000000100000000000000000000000),(131,0x100000000000000000000000),(135,0x2000000000000000800000000000000002000000),(136,0x6000000000000000800000000000000006000000),(137,0x800000000000000000000000),(153,0x400000000000000100040008000000000000000),(154,0x806600c00000000000800040008010004006000000),(155,0xa00400400000000000100040008000005000000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0xa00400400000000000000040028000005000000000)]
 kernelColumns := [(0,0x1a06600c000000000009000c0028010005006000000)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x20000000000000,[2,3]),(0x800000000000000000000000000000000000000,[4,5]),(0x4000000000000000000000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked510 : (cert510).checkIndexedBoundary 180 512 8 sheets510 shadows510 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x2dd80024fc0000d8000002d000036000000000000 = reconX FiberData.topRColumns (cert510).beta := AffineSearchData.rhsChecked510.symm
  have h : (cert510).checkIndexedBoundaryCached 180 512 8 sheets510 shadows510 0x2dd80024fc0000d8000002d000036000000000000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 511. -/
noncomputable def sheets511 : Nat := 0x1b0000000000000024018000000b0000018000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000120010000000000024018000000800000100000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000900200000000000d8004000000300000080000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000d8004000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000001b000000000000000001c0000003000001800000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000012001000000000000001c000000000000100000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000900200000000000fc000000000b00000080000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000fc0000000008000000000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows511 : Nat := 0x1b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b00000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00300000000000fc01c000000b000001800000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices511 : sheets511 = boundedSlice 512 30 8 sheetTable ∧
    shadows511 = boundedSlice 512 30 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt511 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets511) (lane 512 i shadows511) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 30 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices511.1 slices511.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 511. -/
noncomputable def cert511 : AffineMaskCertificate := {
 beta := 0x1b00300000000000fc01c000000b000001800000000
 sectionColumns := [(35,0x240040000008000000000000000),(75,0x200000000000000180000000000000000000000),(95,0x1001000000000000c0000000003000000000000000),(99,0x200000000000000180000000000000000000000000),(101,0x1001000000000000c0000000003000000800000000),(105,0x200200000000000180180000000000001000000000),(124,0x100000000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(147,0x40000000001000000000000000),(148,0x100000000000080000000002000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x40040000008000000000000000),(160,0x640040000008000000000000000),(161,0x800000000000000000000000000)]
 kernelColumns := [(0,0x900100000000000000000000003000000800000000),(1,0x1200200000000000fc01c0000008000001000000000)]
 decoderColumns := [(167,0x1),(168,0x2)]
 dimension := 2
 seeds := [(0x2,[0,1,2,3]),(0x4,[4,5,6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked511 : (cert511).checkIndexedBoundary 180 512 8 sheets511 shadows511 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x36d80000fdb000000000009900000000492000012 = reconX FiberData.topRColumns (cert511).beta := AffineSearchData.rhsChecked511.symm
  have h : (cert511).checkIndexedBoundaryCached 180 512 8 sheets511 shadows511 0x36d80000fdb000000000009900000000492000012 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 512. -/
noncomputable def sheets512 : Nat := 0x1000c00000000000000d0010002003000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000048024010000000800600000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000001c0000000000000048000008000000000600000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000f40080020038000000000004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows512 : Nat := 0x1c00c00000000000480f4000002003800600000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00c00000000000480f4000002003800600000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00c00000000000480f4000002003800600000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00c00000000000480f40000020038006000000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices512 : sheets512 = boundedSlice 512 38 4 sheetTable ∧
    shadows512 = boundedSlice 512 38 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt512 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets512) (lane 512 i shadows512) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 38 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices512.1 slices512.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 512. -/
noncomputable def cert512 : AffineMaskCertificate := {
 beta := 0x1c00c00000000000480f40000020038006000000005
 sectionColumns := [(33,0x1),(35,0x4),(76,0x400000000000000140000000000000000000000),(100,0xc00000000000000500000000010002000000000),(101,0x900000000020004000000000),(105,0x240000000008000000000000),(106,0x800000000000000440000000010000000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(130,0x800000000000000040000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x800000000000000080900000000020004000000000),(154,0x80000000000000000000000000),(155,0xc00c00000000000080c00000000030006000000000),(160,0x400000000000000000000000005),(161,0xc00c00000000000080d00000020030006000000000)]
 kernelColumns := [(0,0x1c00c00000000000480f40000020038006000000005)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked512 : (cert512).checkIndexedBoundary 180 512 4 sheets512 shadows512 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x36900000000000fc000003600000000092400049b = reconX FiberData.topRColumns (cert512).beta := AffineSearchData.rhsChecked512.symm
  have h : (cert512).checkIndexedBoundaryCached 180 512 4 sheets512 shadows512 0x36900000000000fc000003600000000092400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 513. -/
noncomputable def sheets513 : Nat := 0x1000c00200000000000d8010002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0120000000000000024010001000800600100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c0120000000000000000008001000000600100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00200000000000fc0080020008000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows513 : Nat := 0x1c01e00200000000000fc000003000800600100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c01e00200000000000fc000003000800600100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c01e00200000000000fc000003000800600100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c01e00200000000000fc0000030008006001000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices513 : sheets513 = boundedSlice 512 42 4 sheetTable ∧
    shadows513 = boundedSlice 512 42 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt513 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets513) (lane 512 i shadows513) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 42 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices513.1 slices513.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 513. -/
noncomputable def cert513 : AffineMaskCertificate := {
 beta := 0x1c01e00200000000000fc0000030008006001000000
 sectionColumns := [(51,0x1200000000000000d80000000000000001000000),(75,0x200000000000000180000000000000000000000),(76,0x400000000000000140000000000000000000000),(77,0x8000000000000000c0000000000000000000000),(81,0x1000000000000000c00000000000000000000000),(101,0x1e00200000000000c00000000000006001000000),(105,0x240000000008000000000000),(106,0x400000000000000140000000000002000000000),(107,0x1600200000000000cc0000000000002001000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(154,0x801e00200000000000c00000000000006001000000),(155,0x400000000000000000000000000000000000000000),(160,0x801e00200000000000c80000010000006001000000),(161,0x400000000000000000100000020000000000000000)]
 kernelColumns := [(0,0x1c01e00200000000000fc0000030008006001000000)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked513 : (cert513).checkIndexedBoundary 180 512 4 sheets513 shadows513 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x36900036900000fc0000036000009000000000492 = reconX FiberData.topRColumns (cert513).beta := AffineSearchData.rhsChecked513.symm
  have h : (cert513).checkIndexedBoundaryCached 180 512 4 sheets513 shadows513 0x36900036900000fc0000036000009000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 514. -/
noncomputable def sheets514 : Nat := 0x1c0000080000000048000008000000000600000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000004400000000000000f40080020020000004000004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows514 : Nat := 0x1c04400800000000480f4000002002000600400000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001c04400800000000480f40000020020006004000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices514 : sheets514 = boundedSlice 512 46 2 sheetTable ∧
    shadows514 = boundedSlice 512 46 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt514 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets514) (lane 512 i shadows514) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 46 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices514.1 slices514.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 514. -/
noncomputable def cert514 : AffineMaskCertificate := {
 beta := 0x1c04400800000000480f40000020020006004000005
 sectionColumns := [(33,0x1),(35,0x4),(76,0x400000000000000140000000000000000000000),(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(101,0x4000000000000000f00000000020004004000000),(105,0x400800000000000140000000000002000000000),(106,0x400000000000000140000000000002000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x804000000000000080f00000000020004004000000),(154,0x80000000000000000000000000),(155,0xc04000000000000080f00000000020004004000000),(160,0x400000000000000000000000005),(161,0xc04000000000000080e00000020020004004000000)]
 kernelColumns := [(0,0x1c04400800000000480f40000020020006004000005)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked514 : (cert514).checkIndexedBoundary 180 512 2 sheets514 shadows514 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x3690000000000090000003600002400092400049b = reconX FiberData.topRColumns (cert514).beta := AffineSearchData.rhsChecked514.symm
  have h : (cert514).checkIndexedBoundaryCached 180 512 2 sheets514 shadows514 0x3690000000000090000003600002400092400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 515. -/
noncomputable def sheets515 : Nat := 0x104000004000000024002001000800000120000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000c300500200000000000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000104000004000000000006001000000000120000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000e70010020008000000000200002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows515 : Nat := 0x1c40000040000000e7007003000800000120020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c40000040000000e7007003000800000120020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c40000040000000e7007003000800000120020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c40000040000000e70070030008000001200200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices515 : sheets515 = boundedSlice 512 48 4 sheetTable ∧
    shadows515 = boundedSlice 512 48 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt515 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets515) (lane 512 i shadows515) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 48 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices515.1 slices515.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 515. -/
noncomputable def cert515 : AffineMaskCertificate := {
 beta := 0x1c40000040000000e70070030008000001200200000
 sectionColumns := [(35,0x240040000008000000000000000),(45,0xc00000040000000000030030000000000000000000),(75,0xc00000040000000000030030000000000000200000),(93,0x40000000000000030000000000000000000000000),(99,0x40000000000000030000000000000000200000000),(100,0x400000000000000040020020000000000000000000),(101,0x800000000000000040010010000000000000000000),(105,0xc40000040000000030030030000000001200200000),(129,0x40000000000000000000000),(148,0x10000000000000000000000000),(149,0x20000000000000000000000000),(153,0x40000000000000000000000000),(154,0x10010000000000000000000),(155,0x20020000000000000000000),(159,0x40040000008000000000000000),(160,0x640040000008000000000000000),(161,0x800000000000000000000000000),(178,0x10000000000000000000000),(179,0x20000000000000000000000)]
 kernelColumns := [(0,0x1c40000040000000e70070030008000001200200000)]
 decoderColumns := [(168,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1]),(0x4,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked515 : (cert515).checkIndexedBoundary 180 512 4 sheets515 shadows515 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0xd800364b60002400000360000092400002404b6900036 = reconX FiberData.topRColumns (cert515).beta := AffineSearchData.rhsChecked515.symm
  have h : (cert515).checkIndexedBoundaryCached 180 512 4 sheets515 shadows515 0xd800364b60002400000360000092400002404b6900036 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 516. -/
noncomputable def sheets516 : Nat := 0x2000000000000006c000001001c00000000001b001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008200000a80200000010000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000024008001000c00000000001b000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008204800280200100010000000000008
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows516 : Nat := 0x2000000000008206c00a803001c00100000001b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000008206c00a803001c00100000001b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000008206c00a803001c00100000001b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000008206c00a803001c00100000001b0000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices516 : sheets516 = boundedSlice 512 52 4 sheetTable ∧
    shadows516 = boundedSlice 512 52 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt516 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets516) (lane 512 i shadows516) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 52 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices516.1 slices516.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 516. -/
noncomputable def cert516 : AffineMaskCertificate := {
 beta := 0x2000000000008206c00a803001c00100000001b0000
 sectionColumns := [(34,0x800000100000000000000000000),(40,0x4000800100100000000000000000),(41,0x82048008000001000000000001b0000),(59,0x200000000000000000000000000000),(64,0x800000100000000000000010000),(65,0x200000000000000000000000020000),(70,0x4800800000100000000000090000),(71,0x8004800800000100000000000090000),(106,0x8206c008800001800100000001b0000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x8206c008000001800000000001b0000),(137,0x800000000000000000000000),(159,0x200200040000000000000000),(160,0x400000000000000000000000000),(161,0x100000000000000000000),(165,0x200000000000000000000),(166,0x82068008000001000000000001b0000),(167,0x800100100000000000000000)]
 kernelColumns := [(0,0x2000000000008206c00a803001c00100000001b0000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8,[0,1]),(0x10,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked516 : (cert516).checkIndexedBoundary 180 512 4 sheets516 shadows516 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x24000003f000000480000000d80d80012480000da4 = reconX FiberData.topRColumns (cert516).beta := AffineSearchData.rhsChecked516.symm
  have h : (cert516).checkIndexedBoundaryCached 180 512 4 sheets516 shadows516 0x24000003f000000480000000d80d80012480000da4 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 517. -/
noncomputable def sheets517 : Nat := 0x2000000000009006c002003001800000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020088004004001000000018002000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000006e000001001c000000000018001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009000000a80240000010000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000026008001000c000000000018000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009004800280240100010000000000008
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows517 : Nat := 0x2000000000009006e00a803401c001000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000009006e00a803401c001000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000009006e00a803401c001000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000009006e00a803401c001000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000009006e00a803401c001000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000009006e00a803401c0010000000180000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices517 : sheets517 = boundedSlice 512 56 6 sheetTable ∧
    shadows517 = boundedSlice 512 56 6 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt517 (i : Nat) (hi : i < 6) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets517) (lane 512 i shadows517) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 56 6 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices517.1 slices517.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 517. -/
noncomputable def cert517 : AffineMaskCertificate := {
 beta := 0x2000000000009006e00a803401c0010000000180000
 sectionColumns := [(15,0x200240040000000000000000),(34,0x800000100000000000000000000),(35,0xa00000140000000000000000000),(40,0x4000800100100000000000000000),(41,0x9004000a00340140000000000180000),(65,0x1000000000000000000000000000000),(70,0x4000800100100000000000080000),(71,0x8004000a00340140000000000080000),(106,0x9006e00a802001c0010000000180000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x9006e00a002001c0000000000180000),(137,0x800000000000000000000000),(159,0x40000000000000000000),(160,0xe00000140000000000000000000),(161,0x100000000000000000000),(165,0x200040040000000000000000),(166,0x9006000a00340140000000000180000),(167,0x800100100000000000000000)]
 kernelColumns := [(0,0x2000000000009006e00a803401c0010000000180000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8,[0,1]),(0x10,[2,3]),(0x20,[4,5])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked517 : (cert517).checkIndexedBoundary 180 512 6 sheets517 shadows517 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x24900003f000000480000000db6000012480000da4 = reconX FiberData.topRColumns (cert517).beta := AffineSearchData.rhsChecked517.symm
  have h : (cert517).checkIndexedBoundaryCached 180 512 6 sheets517 shadows517 0x24900003f000000480000000db6000012480000da4 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 518. -/
noncomputable def sheets518 : Nat := 0x20800d80000080000000000000090002028000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048005000000000000000002400040000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002080000018008000000000000009000402800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004580480000000000000000240002000000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208004801000800000000000000900080280004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000410040000000000000000024000e000000800400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208000005000000000000000000900040240000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000458000008000000000000024000200c000c0000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows518 : Nat := 0x208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000208045805000800000000000002d0006028000c0040
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices518 : sheets518 = boundedSlice 512 62 8 sheetTable ∧
    shadows518 = boundedSlice 512 62 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt518 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets518) (lane 512 i shadows518) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 62 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices518.1 slices518.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 518. -/
noncomputable def cert518 : AffineMaskCertificate := {
 beta := 0x208045805000800000000000002d0006028000c0040
 sectionColumns := [(45,0x40),(69,0x40000),(70,0x80000),(71,0x8000000000000000000000000080000),(95,0x10000000000000000000000000000000000),(100,0x50008000000000000000000000800080040),(101,0x10008000000000000000000000800080000),(106,0x50008000000000000000000002800080040),(118,0x18000000000000000000000000000000000000),(119,0x10000000000000000000000000000000000000),(123,0x200000000000),(124,0x18000000000000000000000000400000000000),(125,0x58000000000000000000000000400000040000),(131,0x400000000000000000000000000000000000000),(149,0x80000000000000000000000000000000000000000),(153,0x1000200000000000),(155,0x80058000000000000000000004000400000040000),(159,0x9000200000000000),(161,0x80458000000000000000000024000400000040000)]
 kernelColumns := [(0,0x208045805000800000000000002d0006028000c0040)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x400000000,[0,1]),(0x800000000000,[2,3]),(0x8000000000000000000000000000000000,[4,5]),(0x80000000000000000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked518 : (cert518).checkIndexedBoundary 180 512 8 sheets518 shadows518 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x2402400025b480036fc001248000001b000009000 = reconX FiberData.topRColumns (cert518).beta := AffineSearchData.rhsChecked518.symm
  have h : (cert518).checkIndexedBoundaryCached 180 512 8 sheets518 shadows518 0x2402400025b480036fc001248000001b000009000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 519. -/
noncomputable def sheets519 : Nat := 0x208024018000800000000000000900400280020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900008000000000000000024004000000c00040
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows519 : Nat := 0x2080b4018800800000000000002d000002800e0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002080b4018800800000000000002d000002800e00040
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices519 : sheets519 = boundedSlice 512 70 2 sheetTable ∧
    shadows519 = boundedSlice 512 70 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt519 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets519) (lane 512 i shadows519) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 70 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices519.1 slices519.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 519. -/
noncomputable def cert519 : AffineMaskCertificate := {
 beta := 0x2080b4018800800000000000002d000002800e00040
 sectionColumns := [(45,0x40),(71,0x8000000000000000000000000000000),(75,0x200040),(76,0x400000),(77,0x8000000000000000000000000800000),(95,0x8000000000000000000000000000000000),(99,0x88008000000000000000000000800000000),(100,0x188008000000000000000000000800000000),(101,0x8008000000000000000000000800000000),(106,0x188008000000000000000000002800400000),(124,0x100000008000000000000000000000000000000),(125,0x140000008000000000000000000000000000000),(130,0x800000008000000000000000000000000800000),(131,0xa00000008000000000000000000000000a00040),(149,0x80000000000000000000000000000000000000000),(153,0x1000000000000000),(155,0x80140000008000000000000004000000000000000),(159,0x9000000000000000),(161,0x80b40000000000000000000024000000000a00040)]
 kernelColumns := [(0,0x2080b4018800800000000000002d000002800e00040)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked519 : (cert519).checkIndexedBoundary 180 512 2 sheets519 shadows519 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x240240006db000024d80012480000fc0000009000 = reconX FiberData.topRColumns (cert519).beta := AffineSearchData.rhsChecked519.symm
  have h : (cert519).checkIndexedBoundaryCached 180 512 2 sheets519 shadows519 0x240240006db000024d80012480000fc0000009000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 520. -/
noncomputable def sheets520 : Nat := 0x24000000000090002401802000000000020000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000240000000000000124018000000000000200018000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000009000d8004020001000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000001d80040000010000000000180004000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000090006c0100200010000002000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000000016c0100000010000002000180001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000090009000c0200000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000019000c0000000000000000180001
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows520 : Nat := 0x2400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c020001000000200018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400400000009001fc01c0200010000002000180000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices520 : sheets520 = boundedSlice 512 72 8 sheetTable ∧
    shadows520 = boundedSlice 512 72 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt520 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets520) (lane 512 i shadows520) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 72 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices520.1 slices520.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 520. -/
noncomputable def cert520 : AffineMaskCertificate := {
 beta := 0x2400400000009001fc01c0200010000002000180000
 sectionColumns := [(35,0x480080000010000000000000000),(41,0x1000000200000000000000000000),(65,0x1000000000000000000000000000000),(70,0x80000),(71,0x1001000000200000000000000100000),(76,0x400000000000000140000000000000000000000),(100,0x400000000000000140000000000000000000000000),(106,0x400400000000000140140000000000002000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x680080000010000000000000000),(160,0x80080000010000000000000000),(161,0x800000000000000000000000000),(165,0x200000000000000000000)]
 kernelColumns := [(0,0x9001000000200000000000000180000),(1,0x2400400000000000fc01c0000010000002000000000)]
 decoderColumns := [(123,0x1),(169,0x2)]
 dimension := 2
 seeds := [(0x1,[0,1,2,3]),(0x4,[4,5,6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked520 : (cert520).checkIndexedBoundary 180 512 8 sheets520 shadows520 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x264900000d80000000000012db6000000492000012 = reconX FiberData.topRColumns (cert520).beta := AffineSearchData.rhsChecked520.symm
  have h : (cert520).checkIndexedBoundaryCached 180 512 8 sheets520 shadows520 0x264900000d80000000000012db6000000492000012 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 521. -/
noncomputable def sheets521 : Nat := 0x24001b000800000100000000000800080200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400048030009000000000200008000802000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005b000800000100000000002000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000448030009000000000200020000800000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024001f800000000100000000000800040200004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400000038009000000000200008000402000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f800000000100000000002000040000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400038009000000000200020000400000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows521 : Nat := 0x24005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024005f8038009001000000200028000002000040000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices521 : sheets521 = boundedSlice 512 80 8 sheetTable ∧
    shadows521 = boundedSlice 512 80 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt521 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets521) (lane 512 i shadows521) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 80 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices521.1 slices521.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 521. -/
noncomputable def cert521 : AffineMaskCertificate := {
 beta := 0x24005f8038009001000000200028000002000040000
 sectionColumns := [(39,0x38000001000000200000000000000000000),(41,0x1000000200000000000000000000),(63,0x38000001000000000000000000000000000000),(65,0x1000000000000000000000000000000),(69,0x38038001001000000200000000000000040000),(71,0x8000000000000000000000000000000),(94,0x20000001000000200000000000000000000),(95,0x10000000000000000000000000000000000),(106,0x2000000000),(118,0x20000001000000000000000000000000000000),(119,0x10000000000000000000000000000000000000),(124,0xf8038001001000000200000000000000040000),(125,0x80000000000000000000000000000000000000),(131,0x400000000000000000000000000000000000000),(155,0x400000000000000000000000000000000000000000),(159,0x8000000000000000),(161,0x400400000000000000000000020000000000000000),(165,0x200000000000000000000)]
 kernelColumns := [(0,0x1f8038009001000000200000000000000040000),(1,0x2400400000000000000000000028000002000000000)]
 decoderColumns := [(152,0x1),(169,0x2)]
 dimension := 2
 seeds := [(0x400000000000,[0,1,2,3]),(0x800000000000,[4,5,6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked521 : (cert521).checkIndexedBoundary 180 512 8 sheets521 shadows521 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x264900000252480000480012db600003f000000000 = reconX FiberData.topRColumns (cert521).beta := AffineSearchData.rhsChecked521.symm
  have h : (cert521).checkIndexedBoundaryCached 180 512 8 sheets521 shadows521 0x264900000252480000480012db600003f000000000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 522. -/
noncomputable def sheets522 : Nat := 0x2400240180008000000000000008004002c0020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000980008000000000000000020004000000c000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000240000018800000000000000000800200200000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000bc0000008000000000000020002000c00e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400900088000000000000000008001002000800040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c0100008000000000000020001000c00600000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows522 : Nat := 0x2400bc0188008000000000000028000002c00e0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400bc0188008000000000000028000002c00e0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400bc0188008000000000000028000002c00e0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400bc0188008000000000000028000002c00e0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400bc0188008000000000000028000002c00e0004000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400bc0188008000000000000028000002c00e00040
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices522 : sheets522 = boundedSlice 512 88 6 sheetTable ∧
    shadows522 = boundedSlice 512 88 6 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt522 (i : Nat) (hi : i < 6) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets522) (lane 512 i shadows522) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 88 6 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices522.1 slices522.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 522. -/
noncomputable def cert522 : AffineMaskCertificate := {
 beta := 0x2400bc0188008000000000000028000002c00e00040
 sectionColumns := [(45,0x40),(47,0x188008000000000000000000000c00000000),(69,0x1c0000008000000000000000000000000000000),(71,0x8000000000000000000000000000000),(75,0x1c0000008000000000000000000000000200040),(76,0x400000),(77,0x188000000000000000000000000c00800000),(95,0x8000000000000000000000000000000000),(99,0x88008000000000000000000000800000000),(100,0x400000000),(101,0x8008000000000000000000000800000000),(106,0x2400400000),(124,0x100000008000000000000000000000000000000),(125,0x80000000000000000000000000000000000000),(130,0x800188000000000000000000000000c00800000),(131,0xbc0188008000000000000000000000c00a00040),(155,0x400000000000000000000000000000000400000000),(159,0x8000000000000000),(161,0x400bc0188008000000000000020000000800a00040)]
 kernelColumns := [(0,0x2400bc0188008000000000000028000002c00e00040)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x1000000000000,[0,1]),(0x2000000000000,[2,3]),(0x4000000000000,[4,5])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked522 : (cert522).checkIndexedBoundary 180 512 6 sheets522 shadows522 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x249000006d2000024d80012000000fc0000009000 = reconX FiberData.topRColumns (cert522).beta := AffineSearchData.rhsChecked522.symm
  have h : (cert522).checkIndexedBoundaryCached 180 512 6 sheets522 shadows522 0x249000006d2000024d80012000000fc0000009000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 523. -/
noncomputable def sheets523 : Nat := 0x3000000000000000dc000008003800000000003000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000700000000018000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000004c010008001800000000003000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200900600000020018000000000001
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows523 : Nat := 0x3000000000001200dc070008003801800000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000001200dc070008003801800000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000001200dc070008003801800000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000001200dc0700080038018000000030000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices523 : sheets523 = boundedSlice 512 94 4 sheetTable ∧
    shadows523 = boundedSlice 512 94 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt523 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets523) (lane 512 i shadows523) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 94 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices523.1 slices523.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 523. -/
noncomputable def cert523 : AffineMaskCertificate := {
 beta := 0x3000000000001200dc0700080038018000000030000
 sectionColumns := [(28,0x1200d00100080020000000000030000),(34,0x1200400000080000000000000030000),(35,0x400000080000000000000000000),(59,0x200000000000000000000000000000),(64,0x1200400000080000000000000020000),(65,0x200400000080000000000000020000),(105,0x1000000000001200c00000000000000000000030000),(106,0x80400080010010000000000000),(129,0x1000000000001200c00200000000008000000030000),(130,0x80000080010000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(153,0x1200d40100080020000000000030000),(154,0x80000000000000000000000000),(155,0x1200c00100080020000000000030000),(159,0x1000000000000000140300080028008000000000000),(160,0x80000000000000000000),(161,0x1200c00000080000000000000030000)]
 kernelColumns := [(0,0x3000000000001200dc0700080038018000000030000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x1,[0,1]),(0x2,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked523 : (cert523).checkIndexedBoundary 180 512 4 sheets523 shadows523 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0xfc00006c0000000036d80000492000480 = reconX FiberData.topRColumns (cert523).beta := AffineSearchData.rhsChecked523.symm
  have h : (cert523).checkIndexedBoundaryCached 180 512 4 sheets523 shadows523 0xfc00006c0000000036d80000492000480 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 524. -/
noncomputable def sheets524 : Nat := 0x3000000000002082400000010080000000000009008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004802c004000001800000002402000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002080000400010000000000000009020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020806c0040080018000000024008000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000020802401000800080000000240080000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000208000008015000001000000000902000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000002080000080080000000000024008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020800002c00d0000018000000009020
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows524 : Nat := 0x30000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000020820802c005008001800000002d028
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices524 : sheets524 = boundedSlice 512 98 8 sheetTable ∧
    shadows524 = boundedSlice 512 98 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt524 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets524) (lane 512 i shadows524) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 98 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices524.1 slices524.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 524. -/
noncomputable def cert524 : AffineMaskCertificate := {
 beta := 0x30000000000020820802c005008001800000002d028
 sectionColumns := [(35,0x208008000001000000000000002d000),(39,0x8),(41,0x208008000001000000000000002d020),(53,0x80080000010000000000000000000),(57,0x1000),(59,0x80080000010000000000000004000),(63,0x9000),(65,0x2000000000000000000000000009000),(105,0x240000000008000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x80000000010000000000000),(154,0x80000000000000000000000000),(159,0x40000000000000000000),(160,0x208208008001008001000000002d028),(161,0x10000000000020820802c001008001800000002d028),(166,0x208208000001000000000000002d028),(178,0x80000010000000000000000000)]
 kernelColumns := [(0,0x30000000000020820802c005008001800000002d028)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x400000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked524 : (cert524).checkIndexedBoundary 180 512 8 sheets524 shadows524 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b4800120000006c0000000024024024b490006d2 = reconX FiberData.topRColumns (cert524).beta := AffineSearchData.rhsChecked524.symm
  have h : (cert524).checkIndexedBoundaryCached 180 512 8 sheets524 shadows524 0x1b4800120000006c0000000024024024b490006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 525. -/
noncomputable def sheets525 : Nat := 0x30000000000024016800000000500000000000080010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040044004000001800000002003400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002401200080000040000000000008004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000804c0040010018000000020031000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000800401000100080000000200310000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000240120040014004001000000000800400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000001280000080050000000000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000004400c0000018000000008034
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows525 : Nat := 0x300000000000240128044004005001800000002803500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002401280440040050018000000028035000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000024012804400400500180000000280350000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240128044004005001800000002803500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002401280440040050018000000028035000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000024012804400400500180000000280350000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240128044004005001800000002803500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002401280440040050018000000028035
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices525 : sheets525 = boundedSlice 512 106 8 sheetTable ∧
    shadows525 = boundedSlice 512 106 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt525 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets525) (lane 512 i shadows525) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 106 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices525.1 slices525.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 525. -/
noncomputable def cert525 : AffineMaskCertificate := {
 beta := 0x3000000000002401280440040050018000000028035
 sectionColumns := [(29,0x2400000000000000000000000028005),(33,0x1),(34,0x2400200000040000000000000028001),(35,0x2400000000000000000000000028001),(40,0x2400200000040000000000000028011),(41,0x2400000000000000000000000028021),(59,0x400000000000000000000000000000),(63,0x8001),(65,0x2000000000000000000000000008001),(105,0x1200040000040008000000000030),(129,0x40000000000000000000000),(130,0x400000000010000000000000),(135,0x1200000000040000000000000030),(136,0x400000000000000000000000),(154,0x2400080000000000000000000028005),(159,0x40000000000000000000),(160,0x2400080400000010010000000028005),(161,0x1000000000002401280440000050018000000028035),(165,0x1200000040000000000000000030)]
 kernelColumns := [(0,0x3000000000002401280440040050018000000028035)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x80000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked525 : (cert525).checkIndexedBoundary 180 512 8 sheets525 shadows525 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b0000094800006c00000000249000366e400049b = reconX FiberData.topRColumns (cert525).beta := AffineSearchData.rhsChecked525.symm
  have h : (cert525).checkIndexedBoundaryCached 180 512 8 sheets525 shadows525 0x1b0000094800006c00000000249000366e400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 526. -/
noncomputable def sheets526 : Nat := 0x300000000000240264000000008800000000000800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400280040000018000000020026000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000024002404000000080000000000080200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200068004008001800000002000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000200020010008000800000002000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000240024008014000801000000000802000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000002240000080088000000000020008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000002800c0000018000000008026
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows526 : Nat := 0x300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240224028004008801800000002802e
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices526 : sheets526 = boundedSlice 512 114 8 sheetTable ∧
    shadows526 = boundedSlice 512 114 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt526 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets526) (lane 512 i shadows526) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 114 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices526.1 slices526.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 526. -/
noncomputable def cert526 : AffineMaskCertificate := {
 beta := 0x300000000000240224028004008801800000002802e
 sectionColumns := [(29,0x200000040000000000000000006),(33,0x2400200000040000000000000028002),(34,0x2),(35,0x200000040000000000000000002),(39,0x240020000004000000000000002800a),(41,0x200000040000000000000000022),(59,0x400000000000000000000000000000),(63,0x2400200000040000000000000020002),(65,0x400200000040000000000000020002),(105,0x240200000008008000000000006),(129,0x240000000008000000000000006),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x80000000010000000000000),(153,0x240000040000000000000000006),(159,0x40000000000000000000),(160,0x2402000080000080010000000028028),(161,0x100000000000240224028000008801800000002802e),(166,0x2402000000000000000000000028028)]
 kernelColumns := [(0,0x300000000000240224028004008801800000002802e)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x400000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked526 : (cert526).checkIndexedBoundary 180 512 8 sheets526 shadows526 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b0000122400006c00000000249000246f60006d2 = reconX FiberData.topRColumns (cert526).beta := AffineSearchData.rhsChecked526.symm
  have h : (cert526).checkIndexedBoundaryCached 180 512 8 sheets526 shadows526 0x1b0000122400006c00000000249000246f60006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 527. -/
noncomputable def sheets527 : Nat := 0x3000000000002406c0000000018000000000000801000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400ac004000001800000002002000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002400000c00000000000000000008020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068006c004018001800000002001000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000006800240100180008000000020010000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000024000008801400000100000000080200000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000680000008018000000000002001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400000ac00c0000018000000008020
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows527 : Nat := 0x3000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac004018001800000002803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002406800ac0040180018000000028030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices527 : sheets527 = boundedSlice 512 122 8 sheetTable ∧
    shadows527 = boundedSlice 512 122 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt527 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets527) (lane 512 i shadows527) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 122 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices527.1 slices527.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 527. -/
noncomputable def cert527 : AffineMaskCertificate := {
 beta := 0x3000000000002406800ac0040180018000000028030
 sectionColumns := [(35,0x2400000000000000000000000028000),(39,0x4800800000100000000000000010),(40,0x10),(41,0x2400000000000000000000000028020),(59,0x400000000000000000000000000000),(63,0x8000),(65,0x2000000000000000000000000008000),(105,0x240000000008000000000000),(106,0x1000000000002406000ac0000180018000000028030),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x1000000000002406000a40000180008000000028030),(137,0x800000000000000000000000),(159,0x40000000000000000000),(160,0x1000000000000000800240000000008000000000000),(161,0x800000000000000000000000000),(166,0x2406800800000100000000000028030),(167,0x800800000100000000000000000)]
 kernelColumns := [(0,0x3000000000002406800ac0040180018000000028030)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x400000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked527 : (cert527).checkIndexedBoundary 180 512 8 sheets527 shadows527 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b0000360000006c0000000024900024b40000012 = reconX FiberData.topRColumns (cert527).beta := AffineSearchData.rhsChecked527.symm
  have h : (cert527).checkIndexedBoundaryCached 180 512 8 sheets527 shadows527 0x1b0000360000006c0000000024900024b40000012 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 528. -/
noncomputable def sheets528 : Nat := 0x20000000000000006802401000000080000000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000328000048011000001000000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000680000080000000000000014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032800006c009000001800000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000003280000000050000000000000009000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006806c004000001800000001400000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000002080200000010000000000000039000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012004806c0000000018000000024000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows528 : Nat := 0x30000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000032806806c001000001800000001d000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices528 : sheets528 = boundedSlice 512 130 8 sheetTable ∧
    shadows528 = boundedSlice 512 130 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt528 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets528) (lane 512 i shadows528) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 130 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices528.1 slices528.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 528. -/
noncomputable def cert528 : AffineMaskCertificate := {
 beta := 0x30000000000032806806c001000001800000001d000
 sectionColumns := [(34,0x328008000001000000000000001d000),(53,0x80080000010000000000000000000),(57,0x1000),(58,0x280080000010000000000000004000),(59,0x80080000010000000000000004000),(63,0x9000),(64,0x3000000000000000000000000009000),(65,0x2000000000000000000000000009000),(105,0x240000000008000000000000),(106,0x480000000010000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(154,0x80000000000000000000000000),(159,0x328028000001000000000000001d000),(160,0x400000000000000000000000000),(161,0x1000000000000000400240000000008000000000000),(178,0x80000010000000000000000000)]
 kernelColumns := [(0,0x30000000000032806806c001000001800000001d000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x40000000000000000000,[2,3]),(0x80000000000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked528 : (cert528).checkIndexedBoundary 180 512 8 sheets528 shadows528 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x124800000000006c0000000012da4000249000492 = reconX FiberData.topRColumns (cert528).beta := AffineSearchData.rhsChecked528.symm
  have h : (cert528).checkIndexedBoundaryCached 180 512 8 sheets528 shadows528 0x124800000000006c0000000012da4000249000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 529. -/
noncomputable def sheets529 : Nat := 0x20000000000000006402401000000080000000160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000344000048010800001000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000640000080000000000000016000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034400006c008800001800000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000003440000000048000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006406c00400000180000000160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000240024000000000000000000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010404006c0008000018000000020000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows529 : Nat := 0x30000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000034406406c000800001800000001e000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices529 : sheets529 = boundedSlice 512 138 8 sheetTable ∧
    shadows529 = boundedSlice 512 138 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt529 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets529) (lane 512 i shadows529) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 138 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices529.1 slices529.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 529. -/
noncomputable def cert529 : AffineMaskCertificate := {
 beta := 0x30000000000034406406c000800001800000001e000
 sectionColumns := [(34,0x344004000000800000000000001e000),(53,0x40040000008000000000000000000),(57,0x440040000008000000000000004000),(58,0x2000),(59,0x40040000008000000000000004000),(63,0x44004000000800000000000000c000),(64,0x344004000000800000000000000c000),(65,0x244004000000800000000000000c000),(105,0x240000000008000000000000),(106,0x480000000010000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(153,0x40000000000000000000000000),(159,0x344024000000800000000000001e000),(160,0x400000000000000000000000000),(161,0x1000000000000000400240000000008000000000000),(177,0x40000008000000000000000000)]
 kernelColumns := [(0,0x30000000000034406406c000800001800000001e000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x40000000000000000000,[2,3]),(0x80000000000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked529 : (cert529).checkIndexedBoundary 180 512 8 sheets529 shadows529 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x122400000000006c0000000012936000240000492 = reconX FiberData.topRColumns (cert529).beta := AffineSearchData.rhsChecked529.symm
  have h : (cert529).checkIndexedBoundaryCached 180 512 8 sheets529 shadows529 0x122400000000006c0000000012936000240000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 530. -/
noncomputable def sheets530 : Nat := 0x300000000000000108000008005000000000001000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003600000440080000018000000008034
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows530 : Nat := 0x300000000000360108044000005001800000001803500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000003601080440000050018000000018035
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices530 : sheets530 = boundedSlice 512 146 2 sheetTable ∧
    shadows530 = boundedSlice 512 146 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt530 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets530) (lane 512 i shadows530) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 146 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices530.1 slices530.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 530. -/
noncomputable def cert530 : AffineMaskCertificate := {
 beta := 0x3000000000003601080440000050018000000018035
 sectionColumns := [(33,0x1),(34,0x3600000000000000000000000018001),(35,0x4),(40,0x3600000000000000000000000018011),(41,0x24),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8001),(64,0x3000000000000000000000000008001),(65,0x2000000000000000000000000008001),(129,0x40000000000000000000000),(130,0x400000000010000000000000),(135,0x40000000008000000000000),(136,0x400000000000000000000000),(154,0x80000000000000000000000000),(159,0x3601000040000040008000000018035),(160,0x80400000010010000000000000),(161,0x1000000000000000080400000010010000000000000),(165,0x3601000000000000000000000018035)]
 kernelColumns := [(0,0x3000000000003601080440000050018000000018035)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked530 : (cert530).checkIndexedBoundary 180 512 2 sheets530 shadows530 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000094800006c00000000124800366e400049b = reconX FiberData.topRColumns (cert530).beta := AffineSearchData.rhsChecked530.symm
  have h : (cert530).checkIndexedBoundaryCached 180 512 2 sheets530 shadows530 0x120000094800006c00000000124800366e400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 531. -/
noncomputable def sheets531 : Nat := 0x300000000000000204000008008800000000001000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003600000280080000018000000008026
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows531 : Nat := 0x300000000000360204028000008801800000001802e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000360204028000008801800000001802e
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices531 : sheets531 = boundedSlice 512 148 2 sheetTable ∧
    shadows531 = boundedSlice 512 148 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt531 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets531) (lane 512 i shadows531) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 148 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices531.1 slices531.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 531. -/
noncomputable def cert531 : AffineMaskCertificate := {
 beta := 0x300000000000360204028000008801800000001802e
 sectionColumns := [(33,0x3600000000000000000000000018002),(34,0x2),(35,0x4),(39,0x360000000000000000000000001800a),(41,0x24),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x3600000000000000000000000010002),(64,0x600000000000000000000000010002),(65,0x1600000000000000000000000010002),(129,0x200000000008000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x80000000010000000000000),(153,0x40000000000000000000000000),(159,0x40200000008008000000000000),(160,0x360200008000008001000000001802e),(161,0x100000000000360200008000008001000000001802e),(166,0x360200000000000000000000001802e)]
 kernelColumns := [(0,0x300000000000360204028000008801800000001802e)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked531 : (cert531).checkIndexedBoundary 180 512 2 sheets531 shadows531 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000122400006c00000000124800246f60006d2 = reconX FiberData.topRColumns (cert531).beta := AffineSearchData.rhsChecked531.symm
  have h : (cert531).checkIndexedBoundaryCached 180 512 2 sheets531 shadows531 0x120000122400006c00000000124800246f60006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 532. -/
noncomputable def sheets532 : Nat := 0x30000000000104004800004000100000000000480010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240064004000001800000012000400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000010400000080400000000000000048004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020806c0040010018000000120001000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000020802401000100080000001200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000001040000040054000001000000004800400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000002080000080010000000000120001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000104000006404c0000018000000048004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows532 : Nat := 0x300000000001040208064044001001800000016800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000010402080640440010018000000168005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000104020806404400100180000001680050000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000001040208064044001001800000016800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000010402080640440010018000000168005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000104020806404400100180000001680050000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000001040208064044001001800000016800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000010402080640440010018000000168005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices532 : sheets532 = boundedSlice 512 150 8 sheetTable ∧
    shadows532 = boundedSlice 512 150 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt532 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets532) (lane 512 i shadows532) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 150 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices532.1 slices532.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 532. -/
noncomputable def cert532 : AffineMaskCertificate := {
 beta := 0x3000000000010402080640440010018000000168005
 sectionColumns := [(29,0x10402000000400000000000000168005),(33,0x1),(35,0x10402000000400000000000000168001),(41,0x2000000400000000000000000000),(59,0x400000000000000000000000000000),(63,0x8001),(65,0x10002000000400000000000000148001),(69,0x48001),(71,0x10000000000000000000000000048001),(105,0x240000000008000000000000),(129,0x40000000000000000000000),(130,0x400000000010000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(154,0x10402080000400000000000000168005),(159,0x40000000000000000000),(160,0x10402080400400010010000000168005),(161,0x1000000000010402080640400010018000000168005),(166,0x400000000000000000000)]
 kernelColumns := [(0,0x3000000000010402080640440010018000000168005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x80000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked532 : (cert532).checkIndexedBoundary 180 512 8 sheets532 shadows532 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x49b0000004800006c0000000900900009b6400049b = reconX FiberData.topRColumns (cert532).beta := AffineSearchData.rhsChecked532.symm
  have h : (cert532).checkIndexedBoundaryCached 180 512 8 sheets532 shadows532 0x49b0000004800006c0000000900900009b6400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 533. -/
noncomputable def sheets533 : Nat := 0x20000000000000026002401000000080000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000001160000048050000001000000004800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000002600000080000000000000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000116000006c048000001800000004800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000011600000000440000000000000048000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000026006c004000001800000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000010400200000400000000000000078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012024006c0000000018000000120000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows533 : Nat := 0x30000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000116026006c0400000018000000158000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices533 : sheets533 = boundedSlice 512 158 8 sheetTable ∧
    shadows533 = boundedSlice 512 158 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt533 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets533) (lane 512 i shadows533) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 158 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices533.1 slices533.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 533. -/
noncomputable def cert533 : AffineMaskCertificate := {
 beta := 0x30000000000116026006c0400000018000000158000
 sectionColumns := [(34,0x11602000000400000000000000158000),(41,0x2000000400000000000000000000),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8000),(64,0x11002000000400000000000000148000),(65,0x10002000000400000000000000148000),(69,0x48000),(71,0x10000000000000000000000000048000),(105,0x240000000008000000000000),(106,0x480000000010000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(159,0x11602200000400000000000000158000),(160,0x400000000000000000000000000),(161,0x1000000000000000400240000000008000000000000),(166,0x400000000000000000000)]
 kernelColumns := [(0,0x30000000000116026006c0400000018000000158000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x40000000000000000000,[2,3]),(0x80000000000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked533 : (cert533).checkIndexedBoundary 180 512 8 sheets533 shadows533 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x4920000000000006c0000000936480009240000492 = reconX FiberData.topRColumns (cert533).beta := AffineSearchData.rhsChecked533.symm
  have h : (cert533).checkIndexedBoundaryCached 180 512 8 sheets533 shadows533 0x4920000000000006c0000000936480009240000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 534. -/
noncomputable def sheets534 : Nat := 0x30012000000024004800000000100000000010080010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000040064004000002800000002000400000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200000002400000080000000000000001008004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000806c0040010028000000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000020012000000000000802401000100080000010200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000020000240000040014000002000000000800400000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200000000000080000080010000000001020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000024000006400c0000028000000008004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows534 : Nat := 0x300120020000240008064004001002800000102800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200200002400080640040010028000001028005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000024000806400400100280000010280050000000000000000000000000000000000000000000000000000000000000000000000000000000000000300120020000240008064004001002800000102800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200200002400080640040010028000001028005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000024000806400400100280000010280050000000000000000000000000000000000000000000000000000000000000000000000000000000000000300120020000240008064004001002800000102800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200200002400080640040010028000001028005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices534 : sheets534 = boundedSlice 512 166 8 sheetTable ∧
    shadows534 = boundedSlice 512 166 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt534 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets534) (lane 512 i shadows534) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 166 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices534.1 slices534.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 534. -/
noncomputable def cert534 : AffineMaskCertificate := {
 beta := 0x3001200200002400080640040010028000001028005
 sectionColumns := [(29,0x2400000000000000000000000028005),(33,0x1),(35,0x2400000000000000000000000028001),(59,0x400000000000000000000000000000),(63,0x8001),(65,0x2000000000000000000000000008001),(81,0x1000000),(105,0x240000000008000000000000),(107,0x200000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x1200200000000000400000000020000001000000),(131,0x1000200000000000400000000020000001000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(154,0x2400080000000000000000000028005),(159,0x40000000000000000000),(160,0x1200200002400080400000010020000001028005),(161,0x1001200200002400080640000010028000001028005)]
 kernelColumns := [(0,0x3001200200002400080640040010028000001028005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x80000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked534 : (cert534).checkIndexedBoundary 180 512 8 sheets534 shadows534 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b0000369000006c0000000024909000b6400049b = reconX FiberData.topRColumns (cert534).beta := AffineSearchData.rhsChecked534.symm
  have h : (cert534).checkIndexedBoundaryCached 180 512 8 sheets534 shadows534 0x1b0000369000006c0000000024909000b6400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 535. -/
noncomputable def sheets535 : Nat := 0x20012000000000006002401000000080000010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000020000360000048010000002000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200000000000600000080000000000001010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000036000006c008000002800000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200000003600000000040000000000001008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000006006c004000002800000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200000002400200000000000000000001038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000012004006c0000000028000000020000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows535 : Nat := 0x30012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012002000036006006c0000000028000001018000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices535 : sheets535 = boundedSlice 512 174 8 sheetTable ∧
    shadows535 = boundedSlice 512 174 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt535 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets535) (lane 512 i shadows535) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 174 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices535.1 slices535.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 535. -/
noncomputable def cert535 : AffineMaskCertificate := {
 beta := 0x30012002000036006006c0000000028000001018000
 sectionColumns := [(34,0x3600000000000000000000000018000),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8000),(64,0x3000000000000000000000000008000),(65,0x2000000000000000000000000008000),(81,0x1000000),(105,0x240000000008000000000000),(106,0x1200200000000000480000000020000001000000),(107,0x1200000000000000480000000020000001000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(159,0x3600200000000000000000000018000),(160,0x400000000000000000000000000),(161,0x1000000000000000400240000000008000000000000)]
 kernelColumns := [(0,0x30012002000036006006c0000000028000001018000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x40000000000000000000,[2,3]),(0x80000000000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked535 : (cert535).checkIndexedBoundary 180 512 8 sheets535 shadows535 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000036d800006c0000000012489000240000492 = reconX FiberData.topRColumns (cert535).beta := AffineSearchData.rhsChecked535.symm
  have h : (cert535).checkIndexedBoundaryCached 180 512 8 sheets535 shadows535 0x12000036d800006c0000000012489000240000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 536. -/
noncomputable def sheets536 : Nat := 0x30000004000024004800000000100200000000080010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240000000000040064004000001000000202000400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000400002400000080000000020000000008004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000000806c0040010010000002020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000020024000000000000802401000100000000020200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000040000240000040014000003000000000800400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000400000000080000080010020000000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000024000006400c0000010000002008004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows536 : Nat := 0x300240040000240008064004001003000000202800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003002400400002400080640040010030000002028005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000024000806400400100300000020280050000000000000000000000000000000000000000000000000000000000000000000000000000000000000300240040000240008064004001003000000202800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003002400400002400080640040010030000002028005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000024000806400400100300000020280050000000000000000000000000000000000000000000000000000000000000000000000000000000000000300240040000240008064004001003000000202800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003002400400002400080640040010030000002028005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices536 : sheets536 = boundedSlice 512 182 8 sheetTable ∧
    shadows536 = boundedSlice 512 182 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt536 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets536) (lane 512 i shadows536) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 182 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices536.1 slices536.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 536. -/
noncomputable def cert536 : AffineMaskCertificate := {
 beta := 0x3002400400002400080640040010030000002028005
 sectionColumns := [(29,0x2400000000000000000000000028005),(33,0x1),(35,0x2400000000000000000000000028001),(59,0x400000000000000000000000000000),(63,0x8001),(65,0x2000000000000000000000000008001),(82,0x2000000),(105,0x2400400000000000240000000020000002000000),(107,0x2400000000000000240000000020000002000000),(129,0x40000000000000000000000),(130,0x400000000010000000000000),(131,0x400000000000000040000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x2000000000000000200000000000000002000000),(154,0x2400080000000000000000000028005),(159,0x40000000000000000000),(160,0x2400080400000010010000000028005),(161,0x1002400400002400080640000010030000002028005)]
 kernelColumns := [(0,0x3002400400002400080640040010030000002028005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3]),(0x80000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked536 : (cert536).checkIndexedBoundary 180 512 8 sheets536 shadows536 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b000024d80000480000000024912000b6400049b = reconX FiberData.topRColumns (cert536).beta := AffineSearchData.rhsChecked536.symm
  have h : (cert536).checkIndexedBoundaryCached 180 512 8 sheets536 shadows536 0x1b000024d80000480000000024912000b6400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 537. -/
noncomputable def sheets537 : Nat := 0x20024000000000006002401000000000000020100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000040000360000048010000003000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000400000000600000080000020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000036000006c008000001000000200800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000400003600000000040000020000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000006006c004000001000000201000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000400002400200000000000020000000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000012004006c0000000010000002020000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows537 : Nat := 0x30024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030024004000036006006c0000000030000002018000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices537 : sheets537 = boundedSlice 512 190 8 sheetTable ∧
    shadows537 = boundedSlice 512 190 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt537 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets537) (lane 512 i shadows537) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 190 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices537.1 slices537.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 537. -/
noncomputable def cert537 : AffineMaskCertificate := {
 beta := 0x30024004000036006006c0000000030000002018000
 sectionColumns := [(34,0x3600000000000000000000000018000),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8000),(64,0x3000000000000000000000000008000),(65,0x2000000000000000000000000008000),(82,0x2000000),(105,0x2400400000000000240000000020000002000000),(106,0x480000000010000000000000),(107,0x2400000000000000240000000020000002000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x400000000000000040000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x2000000000000000200000000000000002000000),(159,0x3600200000000000000000000018000),(160,0x400000000000000000000000000),(161,0x1002400400000000400240000000020000002000000)]
 kernelColumns := [(0,0x30024004000036006006c0000000030000002018000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x40000000000000000000,[2,3]),(0x80000000000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked537 : (cert537).checkIndexedBoundary 180 512 8 sheets537 shadows537 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000024900000480000000012492000240000492 = reconX FiberData.topRColumns (cert537).beta := AffineSearchData.rhsChecked537.symm
  have h : (cert537).checkIndexedBoundaryCached 180 512 8 sheets537 shadows537 0x12000024900000480000000012492000240000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 538. -/
noncomputable def sheets538 : Nat := 0x2003280000000000000240100000001000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000006800000000004801c000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200480000000000000080000024000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020802000000000006c004000002100000240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000680000000000000080000014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032800000000000006c004000001100000340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003003280000000000000000080000009000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006800000000006c004000000c000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows538 : Nat := 0x30032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030032806800000000006c00c0000005000003400000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices538 : sheets538 = boundedSlice 512 198 8 sheetTable ∧
    shadows538 = boundedSlice 512 198 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt538 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets538) (lane 512 i shadows538) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 198 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices538.1 slices538.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 538. -/
noncomputable def cert538 : AffineMaskCertificate := {
 beta := 0x30032806800000000006c00c0000005000003400000
 sectionColumns := [(52,0x32800800000000006c0000000005000003400000),(75,0x2800800000000000c0000000005000000000000),(76,0x400000),(81,0x2800800000000000c0000000005000001000000),(82,0x32800800000000006c0000000005000001000000),(101,0x80000000000000000000000000000000000),(106,0x32806800000000006c0000000005000003400000),(107,0x32804800000000006c0000000005000003400000),(123,0x40000000001000000000000),(125,0x80000000000000040000000001000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x80080000000000040000000005000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x12800800000000004c0000000005000001000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x30032806800000000006c00c0000005000003400000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked538 : (cert538).checkIndexedBoundary 180 512 8 sheets538 shadows538 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x9000012da400048900000000001b480000000492 = reconX FiberData.topRColumns (cert538).beta := AffineSearchData.rhsChecked538.symm
  have h : (cert538).checkIndexedBoundaryCached 180 512 8 sheets538 shadows538 0x9000012da400048900000000001b480000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 539. -/
noncomputable def sheets539 : Nat := 0x2003440000000000000240100000000000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000006400000000004801c000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001040400000000000000080000020000001200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024002400000000006c004000002600000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000640000000000000080000016000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034400000000000006c004000001000000320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003003440000000000000000080000008000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006400000000006c004000000e000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows539 : Nat := 0x30034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030034406400000000006c00c0000006000003200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices539 : sheets539 = boundedSlice 512 206 8 sheetTable ∧
    shadows539 = boundedSlice 512 206 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt539 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets539) (lane 512 i shadows539) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 206 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices539.1 slices539.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 539. -/
noncomputable def cert539 : AffineMaskCertificate := {
 beta := 0x30034406400000000006c00c0000006000003200000
 sectionColumns := [(52,0x34400400000000006c0000000006000003200000),(75,0x200000),(76,0x4400400000000000c0000000006000000000000),(81,0x1200000),(82,0x3000000000000000600000000000000001200000),(101,0x40000000000000000000000000000000000),(106,0x34406400000000006c0000000006000003200000),(107,0x34404400000000006c0000000006000003200000),(124,0x80000000002000000000000),(125,0x40000000000000080000000002000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x40040000000000080000000006000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001200000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x30034406400000000006c00c0000006000003200000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked539 : (cert539).checkIndexedBoundary 180 512 8 sheets539 shadows539 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x900001293600048000000000001b240000000492 = reconX FiberData.topRColumns (cert539).beta := AffineSearchData.rhsChecked539.symm
  have h : (cert539).checkIndexedBoundaryCached 180 512 8 sheets539 shadows539 0x900001293600048000000000001b240000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 540. -/
noncomputable def sheets540 : Nat := 0x2003600000000000000200100000000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000006000000002404801c0008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012004000000002400000800080200000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240020000000000068004000002000000200000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000600000000240000080008010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000000000000006800400000100000030000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000300360000000000024000008000800800000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000680040000008000000000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows540 : Nat := 0x30036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000002406800c0008000000003000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices540 : sheets540 = boundedSlice 512 214 8 sheetTable ∧
    shadows540 = boundedSlice 512 214 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt540 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets540) (lane 512 i shadows540) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 214 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices540.1 slices540.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 540. -/
noncomputable def cert540 : AffineMaskCertificate := {
 beta := 0x30036006000000002406800c0008000000003000006
 sectionColumns := [(29,0x200000040000000000000000006),(34,0x2),(35,0x200000040000000000000000002),(52,0x3600000000000240680000008000000003000006),(76,0x600000000000240080000008000000000000006),(81,0x1000000),(82,0x3000000000000000600000000000000001000000),(106,0x3600600000000240680000008000000003000006),(107,0x3600400000000240680000008000000003000006),(129,0x240000000008000000000000006),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(153,0x240000040000000000000000006),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x30036006000000002406800c0008000000003000006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked540 : (cert540).checkIndexedBoundary 180 512 8 sheets540 shadows540 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x90000126c000048000000000001b000db6000492 = reconX FiberData.topRColumns (cert540).beta := AffineSearchData.rhsChecked540.symm
  have h : (cert540).checkIndexedBoundaryCached 180 512 8 sheets540 shadows540 0x90000126c000048000000000001b000db6000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 541. -/
noncomputable def sheets541 : Nat := 0x2003600000000000480240100010000000003000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000006000000000004001c0000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012004000000004800000800100200000010000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240020000000000064004000002000000200000400000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000600000000480000080010010000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000000000000006400400000100000030000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000300360000000000048000008001000800000300000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000640040000008000000000004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows541 : Nat := 0x30036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000004806400c0010000000003000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices541 : sheets541 = boundedSlice 512 222 8 sheetTable ∧
    shadows541 = boundedSlice 512 222 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt541 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets541) (lane 512 i shadows541) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 222 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices541.1 slices541.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 541. -/
noncomputable def cert541 : AffineMaskCertificate := {
 beta := 0x30036006000000004806400c0010000000003000005
 sectionColumns := [(29,0x400000080000000000000000005),(33,0x1),(35,0x400000080000000000000000001),(52,0x3600000000000480640000010000000003000005),(76,0x600000000000480040000010000000000000005),(81,0x1000000),(82,0x3000000000000000600000000000000001000000),(106,0x3600600000000480640000010000000003000005),(107,0x3600400000000480640000010000000003000005),(129,0x40000000000000000000000),(130,0x480000000010000000000000005),(131,0x200000000000480000000010000000000000005),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(154,0x480000080000000000000000005),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x30036006000000004806400c0010000000003000005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked541 : (cert541).checkIndexedBoundary 180 512 8 sheets541 shadows541 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x900001200000048000000000001b00092400049b = reconX FiberData.topRColumns (cert541).beta := AffineSearchData.rhsChecked541.symm
  have h : (cert541).checkIndexedBoundaryCached 180 512 8 sheets541 shadows541 0x900001200000048000000000001b00092400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 542. -/
noncomputable def sheets542 : Nat := 0x2003600000000000000040100000000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000006000000012004801c004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200400000001200000080040020000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024002000000000004c004000002000000200003000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000600000001200000080040010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000000000000004c004000001000000300003000000000000000000000000000000000000000000000000000000000000000000000000000000000000003003600000000001200000080040008000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000000004c0040000008000000000030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows542 : Nat := 0x30036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000012004c00c0040000000003000030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices542 : sheets542 = boundedSlice 512 230 8 sheetTable ∧
    shadows542 = boundedSlice 512 230 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt542 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets542) (lane 512 i shadows542) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 230 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices542.1 slices542.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 542. -/
noncomputable def cert542 : AffineMaskCertificate := {
 beta := 0x30036006000000012004c00c0040000000003000030
 sectionColumns := [(35,0x200000040000000000000000000),(40,0x10),(41,0x200000040000000000000000020),(52,0x36000000000012004c0000040000000003000030),(76,0x6000000000000000c0000000000000000000000),(81,0x1000000),(82,0x3000000000001200400000040000000001000030),(106,0x36006000000012004c0000040000000003000030),(107,0x36004000000012004c0000040000000003000030),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x1200000000040000000000000030),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000),(165,0x1200000040000000000000000030)]
 kernelColumns := [(0,0x30036006000000012004c00c0040000000003000030)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked542 : (cert542).checkIndexedBoundary 180 512 8 sheets542 shadows542 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x900001b48000048000000000001b036d80000492 = reconX FiberData.topRColumns (cert542).beta := AffineSearchData.rhsChecked542.symm
  have h : (cert542).checkIndexedBoundaryCached 180 512 8 sheets542 shadows542 0x900001b48000048000000000001b036d80000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 543. -/
noncomputable def sheets543 : Nat := 0x2003600000000002400240100080000000003000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000006000000000000801c000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200400000002400000080080020000001000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024002000000000002c004000002000000200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000600000002400000080080010000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000000000000002c004000001000000300002000000000000000000000000000000000000000000000000000000000000000000000000000000000000003003600000000002400000080080008000003000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000000002c0040000008000000000020
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows543 : Nat := 0x30036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000000024002c00c0080000000003000028
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices543 : sheets543 = boundedSlice 512 238 8 sheetTable ∧
    shadows543 = boundedSlice 512 238 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt543 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets543) (lane 512 i shadows543) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 238 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices543.1 slices543.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 543. -/
noncomputable def cert543 : AffineMaskCertificate := {
 beta := 0x30036006000000024002c00c0080000000003000028
 sectionColumns := [(35,0x400000080000000000000000000),(39,0x8),(41,0x400000080000000000000000020),(52,0x36000000000024002c0000080000000003000028),(76,0x6000000000000000c0000000000000000000000),(81,0x1000000),(82,0x3000000000002400200000080000000001000028),(106,0x36006000000024002c0000080000000003000028),(107,0x36004000000024002c0000080000000003000028),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x2400000000080000000000000028),(137,0x1000000000002400000000080000000001000028),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000),(166,0x2400000080000000000000000028)]
 kernelColumns := [(0,0x30036006000000024002c00c0080000000003000028)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked543 : (cert543).checkIndexedBoundary 180 512 8 sheets543 shadows543 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x900000048000048000000000001b0249000006d2 = reconX FiberData.topRColumns (cert543).beta := AffineSearchData.rhsChecked543.symm
  have h : (cert543).checkIndexedBoundaryCached 180 512 8 sheets543 shadows543 0x900000048000048000000000001b0249000006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 544. -/
noncomputable def sheets544 : Nat := 0x20036000000000002002401000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000060000120000048018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200400000000200000080000020000001030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024002000012000006c000000002000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000600000000200000080000010000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000000012000006c000000001000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003003600000000000200000080000008000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000012000006c0000000008000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows544 : Nat := 0x30036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000012002006c0080000000000003030000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices544 : sheets544 = boundedSlice 512 246 8 sheetTable ∧
    shadows544 = boundedSlice 512 246 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt544 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets544) (lane 512 i shadows544) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 246 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices544.1 slices544.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 544. -/
noncomputable def cert544 : AffineMaskCertificate := {
 beta := 0x30036006000012002006c0080000000000003030000
 sectionColumns := [(35,0x1200000000000000000000000030000),(52,0x36000000000000006c0000000000000003000000),(59,0x200000000000000000000000000000),(64,0x10000),(65,0x1000000000000000000000000010000),(76,0x6000000000000000c0000000000000000000000),(81,0x1000000),(82,0x3000000000000000600000000000000001000000),(106,0x36006000000000006c0000000000000003000000),(107,0x36004000000000006c0000000000000003000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(159,0x1200200000000000000000000030000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x30036006000012002006c0080000000000003030000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked544 : (cert544).checkIndexedBoundary 180 512 8 sheets544 shadows544 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12480000480000000036d9b000000000492 = reconX FiberData.topRColumns (cert544).beta := AffineSearchData.rhsChecked544.symm
  have h : (cert544).checkIndexedBoundaryCached 180 512 8 sheets544 shadows544 0x12480000480000000036d9b000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 545. -/
noncomputable def sheets545 : Nat := 0x20036000000000004002401000000000000030200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000060000240000048014000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001200400002400000000000000020000001008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024002000000004006c004000002000000202000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000600002400000000000000010000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000000000004006c004000001000000302000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003003600000002400000000000000008000003008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000004006c0040000008000000020000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows545 : Nat := 0x30036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030036006000024004006c0040000000000003028000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices545 : sheets545 = boundedSlice 512 254 8 sheetTable ∧
    shadows545 = boundedSlice 512 254 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt545 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets545) (lane 512 i shadows545) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 254 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices545.1 slices545.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 545. -/
noncomputable def cert545 : AffineMaskCertificate := {
 beta := 0x30036006000024004006c0040000000000003028000
 sectionColumns := [(35,0x2400000000000000000000000028000),(52,0x36000000000000006c0000000000000003000000),(59,0x400000000000000000000000000000),(63,0x8000),(65,0x2000000000000000000000000008000),(76,0x6000000000000000c0000000000000000000000),(81,0x1000000),(82,0x3000000000000000600000000000000001000000),(106,0x36006000000000006c0000000000000003000000),(107,0x36004000000000006c0000000000000003000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(159,0x40000000000000000000),(160,0x2400400000000000000000000028000),(161,0x1000000000002400400000000000000000000028000)]
 kernelColumns := [(0,0x30036006000024004006c0040000000000003028000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked545 : (cert545).checkIndexedBoundary 180 512 8 sheets545 shadows545 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b00001248000048000000002491b000240000492 = reconX FiberData.topRColumns (cert545).beta := AffineSearchData.rhsChecked545.symm
  have h : (cert545).checkIndexedBoundaryCached 180 512 8 sheets545 shadows545 0x1b00001248000048000000002491b000240000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 546. -/
noncomputable def sheets546 : Nat := 0x30000008000024036000000000c0000000000008008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000000004000c0040000000000004020010000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000008000000032000000800c0000000000020008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000024000000c00c0000000000004008010
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows546 : Nat := 0x30048008000024032000c00400c0000000004028018000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000024032000c00400c0000000004028018000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000024032000c00400c0000000004028018000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000024032000c00400c0000000004028018
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices546 : sheets546 = boundedSlice 512 262 4 sheetTable ∧
    shadows546 = boundedSlice 512 262 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt546 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets546) (lane 512 i shadows546) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 262 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices546.1 slices546.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 546. -/
noncomputable def cert546 : AffineMaskCertificate := {
 beta := 0x30048008000024032000c00400c0000000004028018
 sectionColumns := [(34,0x2400200000040000000000000028000),(35,0x2400000000000000000000000028000),(39,0x8),(40,0x2400200000040000000000000028010),(59,0x400000000000000000000000000000),(63,0x8000),(65,0x2000000000000000000000000008000),(77,0x8000000000000000c0000000000000000000000),(83,0x8000000000000000c0000000000000004000000),(106,0x800000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x2401200000000040000000000028010),(136,0x48000000024012000c0000040000000004028010),(159,0x40000000000000000000),(160,0x48000000024032000c00000c0000000004028018),(161,0x10048000000024032000c00000c0000000004028018),(165,0x2401200000040000000000000028010),(166,0x2000000000000000000000000008)]
 kernelColumns := [(0,0x30048008000024032000c00400c0000000004028018)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x400000000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked546 : (cert546).checkIndexedBoundary 180 512 4 sheets546 shadows546 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b00001b0000000000000000249240126c00006d2 = reconX FiberData.topRColumns (cert546).beta := AffineSearchData.rhsChecked546.symm
  have h : (cert546).checkIndexedBoundaryCached 180 512 4 sheets546 shadows546 0x1b00001b0000000000000000249240126c00006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 547. -/
noncomputable def sheets547 : Nat := 0x300000080000000028000008001000000000001000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800000003600000640080000000000004008004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows547 : Nat := 0x300480080000360028064000001000000000401800500000000000000000000000000000000000000000000000000000000000000000000000000000000000003004800800003600280640000010000000004018005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices547 : sheets547 = boundedSlice 512 266 2 sheetTable ∧
    shadows547 = boundedSlice 512 266 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt547 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets547) (lane 512 i shadows547) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 266 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices547.1 slices547.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 547. -/
noncomputable def cert547 : AffineMaskCertificate := {
 beta := 0x3004800800003600280640000010000000004018005
 sectionColumns := [(33,0x1),(34,0x3600000000000000000000000018001),(35,0x4),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8001),(64,0x3000000000000000000000000008001),(65,0x2000000000000000000000000008001),(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(106,0x800000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x4800000000000000640000000000000004000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(154,0x80000000000000000000000000),(159,0x3600200000000000000000000018005),(160,0x4800000000000080640000010000000004000000),(161,0x1004800000000000080640000010000000004000000)]
 kernelColumns := [(0,0x3004800800003600280640000010000000004018005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked547 : (cert547).checkIndexedBoundary 180 512 2 sheets547 shadows547 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000004800000000000000124a4000b6400049b = reconX FiberData.topRColumns (cert547).beta := AffineSearchData.rhsChecked547.symm
  have h : (cert547).checkIndexedBoundaryCached 180 512 2 sheets547 shadows547 0x120000004800000000000000124a4000b6400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 548. -/
noncomputable def sheets548 : Nat := 0x3000000800000000440000080008000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000036000006800800000000000040080060000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000080000240004000000000800000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800000001200400680000000000000004020006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows548 : Nat := 0x3004800800003600440680000008000000004018006000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000036004406800000080000000040180060000000000000000000000000000000000000000000000000000000000000000000000000000000000000300480080000360044068000000800000000401800600000000000000000000000000000000000000000000000000000000000000000000000000000000000003004800800003600440680000008000000004018006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices548 : sheets548 = boundedSlice 512 268 4 sheetTable ∧
    shadows548 = boundedSlice 512 268 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt548 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets548) (lane 512 i shadows548) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 268 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices548.1 slices548.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 548. -/
noncomputable def cert548 : AffineMaskCertificate := {
 beta := 0x3004800800003600440680000008000000004018006
 sectionColumns := [(33,0x3600000000000000000000000018002),(34,0x2),(35,0x4),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x3600000000000000000000000010002),(64,0x600000000000000000000000010002),(65,0x1600000000000000000000000010002),(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(106,0x800000000000000000000000000000000000),(129,0x4800000000000000680000000000000004000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(153,0x40000000000000000000000000),(159,0x4800000000000040680000008000000004000000),(160,0x3600400000000000000000000018006),(161,0x1000000000003600400000000000000000000018006)]
 kernelColumns := [(0,0x3004800800003600440680000008000000004018006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x80000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked548 : (cert548).checkIndexedBoundary 180 512 4 sheets548 shadows548 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000002400000000000000124a4000ff6000492 = reconX FiberData.topRColumns (cert548).beta := AffineSearchData.rhsChecked548.symm
  have h : (cert548).checkIndexedBoundaryCached 180 512 4 sheets548 shadows548 0x120000002400000000000000124a4000ff6000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 549. -/
noncomputable def sheets549 : Nat := 0x3000000800000001400000080040000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000036000004c008000000000000400803000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000800002401000000000040000000000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000012004004c0000000000000004020030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows549 : Nat := 0x30048008000036014004c0000040000000004018030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000036014004c0000040000000004018030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000036014004c0000040000000004018030000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000036014004c0000040000000004018030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices549 : sheets549 = boundedSlice 512 272 4 sheetTable ∧
    shadows549 = boundedSlice 512 272 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt549 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets549) (lane 512 i shadows549) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 272 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices549.1 slices549.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 549. -/
noncomputable def cert549 : AffineMaskCertificate := {
 beta := 0x30048008000036014004c0000040000000004018030
 sectionColumns := [(34,0x3600000000000000000000000018000),(40,0x3600000000000000000000000018010),(41,0x20),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8000),(64,0x3000000000000000000000000008000),(65,0x2000000000000000000000000008000),(77,0x8000000000000000c0000000000000000000000),(83,0x8000000000000000c0000000000000004000000),(106,0x800000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x48000000000000004c0000000000000004000000),(136,0x400000000000000000000000),(159,0x48000000036010004c0000040000000004018030),(160,0x400000000000000000000000000),(161,0x1000000000000000400000000000000000000000000),(165,0x3601000000000000000000000018030)]
 kernelColumns := [(0,0x30048008000036014004c0000040000000004018030)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1]),(0x80000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked549 : (cert549).checkIndexedBoundary 180 512 4 sheets549 shadows549 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000090000000000000000124a4036fc0000492 = reconX FiberData.topRColumns (cert549).beta := AffineSearchData.rhsChecked549.symm
  have h : (cert549).checkIndexedBoundaryCached 180 512 4 sheets549 shadows549 0x120000090000000000000000124a4036fc0000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 550. -/
noncomputable def sheets550 : Nat := 0x3000000800000002200000080080000000000010008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000036000002c0080000000000004008020
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows550 : Nat := 0x30048008000036022002c0000080000000004018028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000036022002c0000080000000004018028
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices550 : sheets550 = boundedSlice 512 276 2 sheetTable ∧
    shadows550 = boundedSlice 512 276 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt550 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets550) (lane 512 i shadows550) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 276 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices550.1 slices550.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 550. -/
noncomputable def cert550 : AffineMaskCertificate := {
 beta := 0x30048008000036022002c0000080000000004018028
 sectionColumns := [(34,0x3600000000000000000000000018000),(39,0x8),(41,0x20),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x8000),(64,0x3000000000000000000000000008000),(65,0x2000000000000000000000000008000),(77,0x8000000000000000c0000000000000000000000),(83,0x8000000000000000c0000000000000004000000),(106,0x800000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x48000000000000002c0000000000000004000000),(159,0x3600200000000000000000000018000),(160,0x48000000000020002c0000080000000004000028),(161,0x10048000000000020002c0000080000000004000028),(166,0x2000000000000000000000000028)]
 kernelColumns := [(0,0x30048008000036022002c0000080000000004018028)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked550 : (cert550).checkIndexedBoundary 180 512 2 sheets550 shadows550 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000120000000000000000124a4024b400006d2 = reconX FiberData.topRColumns (cert550).beta := AffineSearchData.rhsChecked550.symm
  have h : (cert550).checkIndexedBoundaryCached 180 512 2 sheets550 shadows550 0x120000120000000000000000124a4024b400006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 551. -/
noncomputable def sheets551 : Nat := 0x3000000800006c0020000010000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800000001200c006c0000000000000004020000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows551 : Nat := 0x3004800800007e00e006c010000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003004800800007e00e006c0100000000000004000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices551 : sheets551 = boundedSlice 512 278 2 sheetTable ∧
    shadows551 = boundedSlice 512 278 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt551 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets551) (lane 512 i shadows551) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 278 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices551.1 slices551.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 551. -/
noncomputable def cert551 : AffineMaskCertificate := {
 beta := 0x3004800800007e00e006c0100000000000004000000
 sectionColumns := [(5,0xe00000000000000000000000000000),(11,0x7000000000000000000000000000000),(34,0x7e00800000100000000000000000000),(53,0x48000000000000006c0000000000000004000000),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(64,0x3000000000000000000000000000000),(65,0x2000000000000000000000000000000),(77,0x8000000000000000c0000000000000000000000),(83,0x4000000000000000600000000000000000000000),(105,0x1000000000007e00400000100000000000000000000),(106,0x1004800800007e004006c0100000000000004000000),(129,0xe00000040000000000000000000000),(130,0xe00000080000000000000000000000),(135,0x7000000200000000000000000000000),(136,0x7000000400000000000000000000000),(159,0x7e00a00000100000000000000000000),(160,0x400000000000000000000000000),(161,0x7e00000000100000000000000000000)]
 kernelColumns := [(0,0x3004800800007e00e006c0100000000000004000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked551 : (cert551).checkIndexedBoundary 180 512 2 sheets551 shadows551 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x360000000000000000000000124a4000480000492 = reconX FiberData.topRColumns (cert551).beta := AffineSearchData.rhsChecked551.symm
  have h : (cert551).checkIndexedBoundaryCached 180 512 2 sheets551 shadows551 0x360000000000000000000000124a4000480000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 552. -/
noncomputable def sheets552 : Nat := 0x3000000800010400000400400000000000000048020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000000000006c004008000000000412000800000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000800000000000000080080000000000120008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000104000002c04c0000000000004048020
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows552 : Nat := 0x30048008000104000002c0440080000000004168028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000104000002c0440080000000004168028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000104000002c0440080000000004168028000000000000000000000000000000000000000000000000000000000000000000000000000000000000030048008000104000002c0440080000000004168028
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices552 : sheets552 = boundedSlice 512 280 4 sheetTable ∧
    shadows552 = boundedSlice 512 280 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt552 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets552) (lane 512 i shadows552) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 280 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices552.1 slices552.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 552. -/
noncomputable def cert552 : AffineMaskCertificate := {
 beta := 0x30048008000104000002c0440080000000004168028
 sectionColumns := [(16,0x10400000000000000000000000168028),(39,0x8),(41,0x20),(59,0x400000000000000000000000000000),(63,0x8000),(65,0x400000000000000000000000020000),(69,0x48008),(71,0x400000000000000000000000120020),(77,0x8000000000000000c0000000000000000000000),(83,0x8000000000000000c0000000000000004000000),(106,0x800000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(135,0x200000000000000000000000),(136,0x48000000000000002c0000000000000004000000),(159,0x40000000000000000000),(160,0x48000000104000002c0400080000000004168028),(161,0x10048000000104000002c0400080000000004168028),(166,0x10400000000400000000000000168028)]
 kernelColumns := [(0,0x30048008000104000002c0440080000000004168028)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x400000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked552 : (cert552).checkIndexedBoundary 180 512 4 sheets552 shadows552 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x49b00001200000000000000090092402db400006d2 = reconX FiberData.topRColumns (cert552).beta := AffineSearchData.rhsChecked552.symm
  have h : (cert552).checkIndexedBoundaryCached 180 512 4 sheets552 shadows552 0x49b00001200000000000000090092402db400006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 553. -/
noncomputable def sheets553 : Nat := 0x20012000000000000002401000c000802000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001004000200000000004580700000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030012000000000000000000800c0000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040002000000000047c0680000108000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows553 : Nat := 0x30052002000000000047c06000c0108020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030052002000000000047c06000c0108020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030052002000000000047c06000c0108020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030052002000000000047c06000c0108020001000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices553 : sheets553 = boundedSlice 512 284 4 sheetTable ∧
    shadows553 = boundedSlice 512 284 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt553 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets553) (lane 512 i shadows553) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 284 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices553.1 slices553.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 553. -/
noncomputable def cert553 : AffineMaskCertificate := {
 beta := 0x30052002000000000047c06000c0108020001000000
 sectionColumns := [(75,0x200000000000000180000000000000000000000),(81,0x200000000000000180000000000000001000000),(83,0x4000000000000000600000000000000000000000),(105,0x240000000008000000000000),(106,0x5200200000000004380000000100020001000000),(107,0x5200000000000004380000000100020001000000),(113,0x1200000000000004580000000100000001000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1200000000000000580000000000000001000000),(143,0x4000000000000000000000000),(159,0x200200040000000000000000),(160,0x400400080000000000000000),(161,0x1000000000000000000640400080008000000000000),(165,0x200000000000000000000),(166,0x400000000000000000000)]
 kernelColumns := [(0,0x30052002000000000047c06000c0108020001000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked553 : (cert553).checkIndexedBoundary 180 512 4 sheets553 shadows553 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x6d200002dd80024fc0000900000009000000000492 = reconX FiberData.topRColumns (cert553).beta := AffineSearchData.rhsChecked553.symm
  have h : (cert553).checkIndexedBoundaryCached 180 512 4 sheets553 shadows553 0x6d200002dd80024fc0000900000009000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 554. -/
noncomputable def sheets554 : Nat := 0x20024000000000000002401000c00000200020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100400040000000000458070000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003004000400000000004100640000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000000006c00400c0010020002000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows554 : Nat := 0x30064004000000000047c06000c0110020002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030064004000000000047c06000c0110020002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030064004000000000047c06000c0110020002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030064004000000000047c06000c0110020002000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices554 : sheets554 = boundedSlice 512 288 4 sheetTable ∧
    shadows554 = boundedSlice 512 288 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt554 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets554) (lane 512 i shadows554) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 288 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices554.1 slices554.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 554. -/
noncomputable def cert554 : AffineMaskCertificate := {
 beta := 0x30064004000000000047c06000c0110020002000000
 sectionColumns := [(76,0x400000000000000140000000000000000000000),(82,0x400000000000000140000000000000002000000),(83,0x4000000000000000600000000000000000000000),(105,0x6400400000000004540000000100020002000000),(106,0x480000000010000000000000),(107,0x6400000000000004540000000100020002000000),(113,0x2400000000000004340000000100000002000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x2400000000000000340000000000000002000000),(143,0x4000000000000000000000000),(159,0x200200040000000000000000),(160,0x400400080000000000000000),(161,0x1006400400000000004140400080100020002000000),(165,0x200000000000000000000),(166,0x400000000000000000000)]
 kernelColumns := [(0,0x30064004000000000047c06000c0110020002000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x40000000000000000000,[0,1]),(0x100000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked554 : (cert554).checkIndexedBoundary 180 512 4 sheets554 shadows554 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x6d200003f900024d80000900000012000000000492 = reconX FiberData.topRColumns (cert554).beta := AffineSearchData.rhsChecked554.symm
  have h : (cert554).checkIndexedBoundaryCached 180 512 4 sheets554 shadows554 0x6d200003f900024d80000900000012000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 555. -/
noncomputable def sheets555 : Nat := 0x200a60000000000000024010000000000000b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000016000000000004801c000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003008200400000000000000080000020000009000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024012000000000006c00400001a0000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000016000000000000000800001900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a6000000000000006c004000001000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a60000000000000000008000000800000b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000016000000000006c0040000188000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows555 : Nat := 0x300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300a6016000000000006c00c000018000000b000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices555 : sheets555 = boundedSlice 512 292 8 sheetTable ∧
    shadows555 = boundedSlice 512 292 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt555 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets555) (lane 512 i shadows555) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 292 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices555.1 slices555.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 555. -/
noncomputable def cert555 : AffineMaskCertificate := {
 beta := 0x300a6016000000000006c00c000018000000b000000
 sectionColumns := [(52,0xa6010000000000006c000000018000000b000000),(76,0x6000000000000000c0000000000000000000000),(81,0x1000000),(82,0xa001000000000000600000000180000009000000),(87,0x9000000),(106,0xa6016000000000006c000000018000000b000000),(107,0xa6014000000000006c000000018000000b000000),(113,0x1000000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x8001000000000000400000000180000009000000),(142,0x400000000080000000000000),(143,0x8000000000000000400000000080000009000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x300a6016000000000006c00c000018000000b000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked555 : (cert555).checkIndexedBoundary 180 512 8 sheets555 shadows555 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x9000da448000048000000000025b000000000492 = reconX FiberData.topRColumns (cert555).beta := AffineSearchData.rhsChecked555.symm
  have h : (cert555).checkIndexedBoundaryCached 180 512 8 sheets555 shadows555 0x9000da448000048000000000025b000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 556. -/
noncomputable def sheets556 : Nat := 0x2011600000000000000240100000040000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000026000000000004801c000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003001202400000000000000080000120000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000104002000000000006c004000006000001200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000002600000000000000080000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000116000000000000006c004000005000001300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003011600000000000000000080000048000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000026000000000006c0040000108000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows556 : Nat := 0x30116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030116026000000000006c00c0000140000013000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices556 : sheets556 = boundedSlice 512 300 8 sheetTable ∧
    shadows556 = boundedSlice 512 300 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt556 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets556) (lane 512 i shadows556) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 300 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices556.1 slices556.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 556. -/
noncomputable def cert556 : AffineMaskCertificate := {
 beta := 0x30116026000000000006c00c0000140000013000000
 sectionColumns := [(52,0x116020000000000006c0000000140000013000000),(76,0x6000000000000000c0000000000000000000000),(81,0x1000000),(82,0x11002000000000000600000000140000011000000),(88,0x11002000000000000600000000140000001000000),(106,0x116026000000000006c0000000140000013000000),(107,0x116024000000000006c0000000140000013000000),(113,0x2000000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(141,0x200000000040000000000000),(143,0x1002000000000000400000000100000001000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1000000000000000000000080000000000000000000)]
 kernelColumns := [(0,0x30116026000000000006c00c0000140000013000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000,[0,1]),(0x10000000000000,[2,3]),(0x20000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked556 : (cert556).checkIndexedBoundary 180 512 8 sheets556 shadows556 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x900093648000948000000000049b000000000492 = reconX FiberData.topRColumns (cert556).beta := AffineSearchData.rhsChecked556.symm
  have h : (cert556).checkIndexedBoundaryCached 180 512 8 sheets556 shadows556 0x900093648000948000000000049b000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 557. -/
noncomputable def sheets557 : Nat := 0x34400000400000000000a0008008004003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004004000000000000900080200140000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000009000802003c000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010404000400000000000a0008020004001200000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows557 : Nat := 0x30404000400000000900a802801c004003200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030404000400000000900a802801c004003200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030404000400000000900a802801c004003200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030404000400000000900a802801c004003200200000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices557 : sheets557 = boundedSlice 512 308 4 sheetTable ∧
    shadows557 = boundedSlice 512 308 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt557 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets557) (lane 512 i shadows557) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 308 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices557.1 slices557.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 557. -/
noncomputable def cert557 : AffineMaskCertificate := {
 beta := 0x30404000400000000900a802801c004003200200000
 sectionColumns := [(75,0x200000),(99,0x200000000),(101,0x40000000000000000000000000000000000),(105,0x1200200000),(106,0x2000000000),(125,0x40000000000000010020020004000000000000000),(129,0x40400040000000010020020004004000000000000),(130,0x80000000000000000000000),(131,0x40000040000000010020020004004000000000000),(148,0x10000000000000000000000000),(149,0x40000000000000010000000000000000000000000),(153,0x8008000000000000000000),(154,0x80000000000000000000000000),(155,0x20020000000000000000000),(159,0x4040004000000001002802800c004000000000000),(160,0x80080000010000000000000000),(161,0x1000000000000000080080000010000001200200000),(177,0x8000000000000000000000),(179,0x20000000000000000000000)]
 kernelColumns := [(0,0x30404000400000000900a802801c004003200200000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000000000000000,[0,1]),(0x400000000000000000000000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked557 : (cert557).checkIndexedBoundary 180 512 4 sheets557 shadows557 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0xb40012b76000fe400001200001b240000240024900024 = reconX FiberData.topRColumns (cert557).beta := AffineSearchData.rhsChecked557.symm
  have h : (cert557).checkIndexedBoundaryCached 180 512 4 sheets557 shadows557 0xb40012b76000fe400001200001b240000240024900024 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 558. -/
noncomputable def sheets558 : Nat := (Nat.lor 0x34400000000000000000a0008008002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004006400000000000900080200140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000320004000000000009000802000c000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002406000000000000000a00080100020002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200024000000000009000802003c000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010404000000000000000a00080200020012000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000304000000000000009000802000a000003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006400000000000000a0008016002000000000000 (Nat.shiftLeft 0x40304000000000000000002002000800000320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000640000000000090088008014002000000000000 4096))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows558 : Nat := (Nat.lor 0x30406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000 (Nat.shiftLeft 0x30406400000000000900a802801c002003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030406400000000000900a802801c002003200000000 4096))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices558 : sheets558 = boundedSlice 512 312 10 sheetTable ∧
    shadows558 = boundedSlice 512 312 10 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt558 (i : Nat) (hi : i < 10) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets558) (lane 512 i shadows558) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 312 10 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices558.1 slices558.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 558. -/
noncomputable def cert558 : AffineMaskCertificate := {
 beta := 0x30406400000000000900a802801c002003200000000
 sectionColumns := [(99,0x200000000),(100,0x400400000000000100a0020004002000000000000),(105,0x1200000000),(106,0x400400000000000100a0020004002002000000000),(124,0x40040000000000010020020004000000000000000),(125,0x40000000000000010020020004000000000000000),(129,0x600000000000000080000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(148,0x10000000000000000000000000),(149,0x40000000000000010000000000000000000000000),(153,0x8008000000000000000000),(154,0x80000000000000000000000000),(155,0x20020000000000000000000),(159,0x600000000000000088008008000000000000000),(160,0x80080000010000000000000000),(161,0x1000000000000000080080000010000001200000000),(177,0x8000000000000000000000),(179,0x20000000000000000000000)]
 kernelColumns := [(0,0x30406400000000000900a802801c002003200000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x2000000000000000,[0,1]),(0x20000000000000000,[2,3]),(0x200000000000000000000000000000000000000000,[4,5]),(0x400000000000000000000000000000000000000000,[6,7]),(0x400000000000000000000000000000000000000000000,[8,9])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked558 : (cert558).checkIndexedBoundary 180 512 10 sheets558 shadows558 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0xb40012b7600025200001200001b240000000024900024 = reconX FiberData.topRColumns (cert558).beta := AffineSearchData.rhsChecked558.symm
  have h : (cert558).checkIndexedBoundaryCached 180 512 10 sheets558 shadows558 0xb40012b7600025200001200001b240000000024900024 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 559. -/
noncomputable def sheets559 : Nat := 0x30c00009e000002000000000000900200000000090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900000000000000004000012002000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c09008e000002000000000000900100000080090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000004000012001000000000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows559 : Nat := 0x30c09009e000002000000400001b000000000800900000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c09009e000002000000400001b000000000800900000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c09009e000002000000400001b000000000800900000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c09009e000002000000400001b000000000800900
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices559 : sheets559 = boundedSlice 512 322 4 sheetTable ∧
    shadows559 = boundedSlice 512 322 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt559 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets559) (lane 512 i shadows559) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 322 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices559.1 slices559.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 559. -/
noncomputable def cert559 : AffineMaskCertificate := {
 beta := 0x30c09009e000002000000400001b000000000800900
 sectionColumns := [(41,0x1c0000020000004000000000000000000100),(46,0x20000004000000000000000000000),(47,0x1c0000020000004000000000000000000000),(53,0x1c0000020000004000000000000000000800),(77,0x1c0000020000004000000000000000800000),(94,0x1e0000020000004000000000000000000100),(100,0xc0000020000004000000000000000000000),(101,0x80000020000004000000000000000000000),(106,0x9c0000020000004000000000000000000800),(124,0x100000000000000000000000000000000000000),(130,0x8001c0000020000004000000000000000800000),(148,0xc00001e0000020000004000000000000000000100),(149,0x800001e0000020000004000000000000000000100),(153,0x1000000000000000),(154,0xc01001e0000020000004000002000000000000100),(159,0x9000000000000000),(160,0xc0900020000000000000000012000000000800100),(161,0x10c0900020000000000000000012000000000800100),(173,0x4000000000000000000000)]
 kernelColumns := [(0,0x30c09009e000002000000400001b000000000800900)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x1000000000000,[0,1]),(0x2000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked559 : (cert559).checkIndexedBoundary 180 512 4 sheets559 shadows559 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x240120120006db000012000000000000900000924000 = reconX FiberData.topRColumns (cert559).beta := AffineSearchData.rhsChecked559.symm
  have h : (cert559).checkIndexedBoundaryCached 180 512 4 sheets559 shadows559 0x240120120006db000012000000000000900000924000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 560. -/
noncomputable def sheets560 : Nat := 0x210000000000000000024010001b00800480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000900000000000000d801000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000310000000000000000000008001b00000480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900000000000000fc008000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000900000000000000900040000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000006c004001b018004800000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows560 : Nat := 0x3100900000000000000fc000001b03800480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003100900000000000000fc000001b03800480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003100900000000000000fc000001b03800480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003100900000000000000fc000001b03800480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003100900000000000000fc000001b03800480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003100900000000000000fc000001b038004800000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices560 : sheets560 = boundedSlice 512 326 6 sheetTable ∧
    shadows560 = boundedSlice 512 326 6 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt560 (i : Nat) (hi : i < 6) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets560) (lane 512 i shadows560) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 326 6 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices560.1 slices560.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 560. -/
noncomputable def cert560 : AffineMaskCertificate := {
 beta := 0x3100900000000000000fc000001b038004800000000
 sectionColumns := [(77,0x8000000000000000c0000000000000000000000),(95,0x8000000000000009c0000000020004800000000),(101,0x8000000000000009c0000000020004000000000),(105,0x240000000008000000000000),(106,0x480000000010000000000000),(107,0x900000000020000000000000),(124,0x100000000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(148,0x1008000000000000009c0000000020004800000000),(153,0x1000000000000000),(154,0x1009000000000000009c0000002020004800000000),(159,0x40000009000000000000000),(160,0x100900000000000000940000012020004800000000),(161,0x1100900000000000000b00000012028004800000000)]
 kernelColumns := [(0,0x3100900000000000000fc000001b038004800000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x40000000000000000000,[0,1]),(0x80000000000000000000,[2,3]),(0x100000000000000000000,[4,5])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked560 : (cert560).checkIndexedBoundary 180 512 6 sheets560 shadows560 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000006db000fc0000024900000000000000492 = reconX FiberData.topRColumns (cert560).beta := AffineSearchData.rhsChecked560.symm
  have h : (cert560).checkIndexedBoundaryCached 180 512 6 sheets560 shadows560 0x120000006db000fc0000024900000000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 561. -/
noncomputable def sheets561 : Nat := 0x310000080000000000000008001b00000480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004100000000000000fc0080000020000004000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows561 : Nat := 0x3104100800000000000fc000001b02000480400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003104100800000000000fc000001b020004804000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices561 : sheets561 = boundedSlice 512 332 2 sheetTable ∧
    shadows561 = boundedSlice 512 332 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt561 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets561) (lane 512 i shadows561) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 332 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices561.1 slices561.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 561. -/
noncomputable def cert561 : AffineMaskCertificate := {
 beta := 0x3104100800000000000fc000001b020004804000000
 sectionColumns := [(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(95,0x4000000000000000f00000000020004804000000),(101,0x4000000000000000f00000000020004004000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(124,0x100000000000000000000000000000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(148,0x104000000000000000f00000000020004804000000),(153,0x1000000000000000),(154,0x104100000000000000f00000002020004804000000),(159,0x40000009000000000000000),(160,0x104100000000000000f80000012020004804000000),(161,0x1104100000000000000f80000012020004804000000)]
 kernelColumns := [(0,0x3104100800000000000fc000001b020004804000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked561 : (cert561).checkIndexedBoundary 180 512 2 sheets561 shadows561 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000006db000900000024900024000000000492 = reconX FiberData.topRColumns (cert561).beta := AffineSearchData.rhsChecked561.symm
  have h : (cert561).checkIndexedBoundaryCached 180 512 2 sheets561 shadows561 0x120000006db000900000024900024000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 562. -/
noncomputable def sheets562 : Nat := 0x2000200000000000dc000010000800000000003000200000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000001200000540000000010001000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows562 : Nat := 0x3200200000001200dc054010000801000100003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000001200dc0540100008010001000030000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices562 : sheets562 = boundedSlice 512 334 2 sheetTable ∧
    shadows562 = boundedSlice 512 334 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt562 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets562) (lane 512 i shadows562) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 334 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices562.1 slices562.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 562. -/
noncomputable def cert562 : AffineMaskCertificate := {
 beta := 0x3200200000001200dc0540100008010001000030000
 sectionColumns := [(34,0x800000100000000000000000000),(35,0x1200800000100000000000000030000),(59,0x200000000000000000000000000000),(64,0x800000100000000000000010000),(65,0x1000800000100000000000000010000),(75,0x1200000000001200d80000000000000001000030000),(99,0x200000000000000180000000000000000000000000),(105,0x1000000000001200c00000000000000000000030000),(106,0x1200200000001200d80500000000010001000030000),(129,0x40000000000000000000000),(130,0x1200200000001200d80100000000000001000030000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x40040000008000000000000000),(160,0x1200c00000100000000000000030000),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x3200200000001200dc0540100008010001000030000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked562 : (cert562).checkIndexedBoundary 180 512 2 sheets562 shadows562 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x36d80000fc0000480000009036d80000492000936 = reconX FiberData.topRColumns (cert562).beta := AffineSearchData.rhsChecked562.symm
  have h : (cert562).checkIndexedBoundaryCached 180 512 2 sheets562 shadows562 0x36d80000fc0000480000009036d80000492000936 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 563. -/
noncomputable def sheets563 : Nat := 0x320000000000410000018002000000000100001b00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000480480040000010000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000000000004800001000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000120000000000410000050016000001000100001b004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows563 : Nat := 0x320020000000410048050006000001000100001b0060000000000000000000000000000000000000000000000000000000000000000000000000000000000000320020000000410048050006000001000100001b0060000000000000000000000000000000000000000000000000000000000000000000000000000000000000320020000000410048050006000001000100001b0060000000000000000000000000000000000000000000000000000000000000000000000000000000000000320020000000410048050006000001000100001b006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices563 : sheets563 = boundedSlice 512 336 4 sheetTable ∧
    shadows563 = boundedSlice 512 336 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt563 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets563) (lane 512 i shadows563) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 336 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices563.1 slices563.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 563. -/
noncomputable def cert563 : AffineMaskCertificate := {
 beta := 0x320020000000410048050006000001000100001b006
 sectionColumns := [(34,0x2),(35,0x4),(52,0x400000000000000000000000001b002),(57,0x1000),(58,0x4000000000000000000000000019002),(63,0x9000),(64,0x4000000000000000000000000009000),(99,0x20000000000410008000002000000000000001b002),(105,0x20000000000410008000002000000000100001b002),(106,0x200000000000000500000000010000000000000),(130,0x200000000000000100000000000000000000000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(154,0x80000000000000000000000000),(155,0x410000000002000000000000001b002),(159,0x40000000000000000000),(160,0x400000000000000000000000004),(161,0x120000000000410048000002000000000100001b006),(179,0x410000000000000000000000001b002)]
 kernelColumns := [(0,0x320020000000410048050006000001000100001b006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x100000000000000000000,[0,1]),(0x80000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked563 : (cert563).checkIndexedBoundary 180 512 4 sheets563 shadows563 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b480000d80000480000009000000000fff000936 = reconX FiberData.topRColumns (cert563).beta := AffineSearchData.rhsChecked563.symm
  have h : (cert563).checkIndexedBoundaryCached 180 512 4 sheets563 shadows563 0x1b480000d80000480000009000000000fff000936 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 564. -/
noncomputable def sheets564 : Nat := 0x2000200000004800f80000000000000000000028002000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000012008005000000000100010000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000320000000000480020018000000000000100002800400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000001200580480000000010000000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows564 : Nat := 0x3200200000005a0078050000000001000100002800600000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000005a0078050000000001000100002800600000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000005a0078050000000001000100002800600000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000005a00780500000000010001000028006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices564 : sheets564 = boundedSlice 512 340 4 sheetTable ∧
    shadows564 = boundedSlice 512 340 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt564 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets564) (lane 512 i shadows564) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 340 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices564.1 slices564.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 564. -/
noncomputable def cert564 : AffineMaskCertificate := {
 beta := 0x3200200000005a00780500000000010001000028006
 sectionColumns := [(33,0x5a00000000000000000000000028004),(34,0x2),(35,0x4),(58,0x800000000000000000000000000000),(59,0xa00000000000000000000000000000),(63,0x5a00000000000000000000000020004),(64,0x1a00000000000000000000000020004),(65,0xa00000000000000000000000020004),(99,0x200000000000000180000000000000000000000000),(105,0x200000000000000180000000000000001000000000),(106,0x200000000000000500000000010000000000000),(130,0x200000000000000100000000000000000000000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x200000000000000000000000006),(160,0x5a00400000000000000000000028000),(161,0x1200000000005a00580000000000000001000028000)]
 kernelColumns := [(0,0x3200200000005a00780500000000010001000028006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000000,[0,1]),(0x800000000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked564 : (cert564).checkIndexedBoundary 180 512 4 sheets564 shadows564 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12d80000d80000480000009036d80000fe4000936 = reconX FiberData.topRColumns (cert564).beta := AffineSearchData.rhsChecked564.symm
  have h : (cert564).checkIndexedBoundaryCached 180 512 4 sheets564 shadows564 0x12d80000d80000480000009036d80000fe4000936 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 565. -/
noncomputable def sheets565 : Nat := 0x3200000000006c00000180080000000001000010004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000001804800400000100000000200020000000000000000000000000000000000000000000000000000000000000000000000000000000000000200020000000000018000010000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000006c000005001c0000010001000010004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows565 : Nat := 0x3200200000006c001805000c000001000100003000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000006c001805000c000001000100003000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000006c001805000c000001000100003000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003200200000006c001805000c0000010001000030006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices565 : sheets565 = boundedSlice 512 344 4 sheetTable ∧
    shadows565 = boundedSlice 512 344 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt565 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets565) (lane 512 i shadows565) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 344 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices565.1 slices565.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 565. -/
noncomputable def cert565 : AffineMaskCertificate := {
 beta := 0x3200200000006c001805000c0000010001000030006
 sectionColumns := [(29,0x6c00000000000000000000000030006),(34,0x2),(35,0x6c00000000000000000000000030002),(58,0x800000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x4800000000000000000000000010002),(64,0x800000000000000000000000010002),(65,0x6800000000000000000000000010002),(99,0x200000000006c00180000000000000000000030006),(105,0x200000000006c00180000000000000001000030006),(106,0x200000000000000500000000010000000000000),(130,0x200000000000000100000000000000000000000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(154,0x6c00080000000000000000000030006),(155,0x100000000000000000000000000),(159,0x40000000000000000000),(160,0x80000000000000000000),(161,0x1200000000006c00180000080000000001000030006)]
 kernelColumns := [(0,0x3200200000006c001805000c0000010001000030006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x100000000000000000000,[0,1]),(0x80000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked565 : (cert565).checkIndexedBoundary 180 512 4 sheets565 shadows565 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x9d80000d80000480000009024900000da4000936 = reconX FiberData.topRColumns (cert565).beta := AffineSearchData.rhsChecked565.symm
  have h : (cert565).checkIndexedBoundaryCached 180 512 4 sheets565 shadows565 0x9d80000d80000480000009024900000da4000936 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 566. -/
noncomputable def sheets566 : Nat := 0x2000200000000000650008020022000002000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000012004000000000000000600080200020010000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000320000000000000065000802001200000300000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000000060008010002000000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows566 : Nat := 0x3200600000000000650068028002002003000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000032006000000000006500680280020020030000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000320060000000000065006802800200200300000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000003200600000000000650068028002002003000000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices566 : sheets566 = boundedSlice 512 348 4 sheetTable ∧
    shadows566 = boundedSlice 512 348 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt566 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets566) (lane 512 i shadows566) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 348 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices566.1 slices566.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 566. -/
noncomputable def cert566 : AffineMaskCertificate := {
 beta := 0x3200600000000000650068028002002003000000003
 sectionColumns := [(29,0x40008008000000000000000000),(33,0x1),(34,0x2),(100,0x200600000000000050068028002002000000000000),(105,0x1000000000),(106,0x200600000000000050068028002002002000000000),(124,0x200000000000000050028028002000000000000000),(129,0x40000000000000000000000),(130,0x600000000000000040000000000000000000000),(131,0x400000000000000040000000000000000000000),(148,0x10000000000000000000000000),(153,0x8008000000000000000000),(154,0x200000000000000040028028000000000000000000),(155,0x40028028000000000000000000),(159,0x200000000000000000000000002),(160,0x400000000000000000000000001),(161,0x1000000000000000400000000000000001000000001),(177,0x8000000000000000000000),(179,0x40028008000000000000000000)]
 kernelColumns := [(0,0x3200600000000000650068028002002003000000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x10000000000000000,[0,1]),(0x20000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked566 : (cert566).checkIndexedBoundary 180 512 4 sheets566 shadows566 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0xb400126c000049200001200001b0000000004b690002d = reconX FiberData.topRColumns (cert566).beta := AffineSearchData.rhsChecked566.symm
  have h : (cert566).checkIndexedBoundaryCached 180 512 4 sheets566 shadows566 0xb400126c000049200001200001b0000000004b690002d DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 567. -/
noncomputable def sheets567 : Nat := 0x2001000000000000d800401000000000000010000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000120000020000000024050004000802000100000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000000000000fc000010000800000000100000200000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000200000000000540040000020001000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows567 : Nat := 0x3201000200000000fc054014000802000100100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200000000fc054014000802000100100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200000000fc054014000802000100100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200000000fc0540140008020001001000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices567 : sheets567 = boundedSlice 512 352 4 sheetTable ∧
    shadows567 = boundedSlice 512 352 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt567 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets567) (lane 512 i shadows567) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 352 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices567.1 slices567.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 567. -/
noncomputable def cert567 : AffineMaskCertificate := {
 beta := 0x3201000200000000fc0540140008020001001000000
 sectionColumns := [(29,0x40040040008000000000000000),(34,0x800000100000000000000000000),(35,0xa00000140000000000000000000),(75,0x1200000000000000fc0040000008000001000000000),(81,0x1200000000000000fc0040000008000001001000000),(99,0x2000000000000001c0040040008000000000000000),(105,0x1000000000000000e00000040000000000000000000),(106,0x1201000200000000fc0540000008020001001000000),(107,0x1201000000000000fc0540000008020001001000000),(129,0x40000000000000000000000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(137,0x1201000000000000fc0440000008000001001000000),(153,0x40040008000000000000000),(154,0xc0040040008000000000000000),(155,0x100000000000000000000000000),(159,0x40000000000000000000),(160,0xe00000140000000000000000000),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x3201000200000000fc0540140008020001001000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x2,[0,1]),(0x4,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked567 : (cert567).checkIndexedBoundary 180 512 4 sheets567 shadows567 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x3fd80036240000480000009000009000492000936 = reconX FiberData.topRColumns (cert567).beta := AffineSearchData.rhsChecked567.symm
  have h : (cert567).checkIndexedBoundaryCached 180 512 4 sheets567 shadows567 0x3fd80036240000480000009000009000492000936 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 568. -/
noncomputable def sheets568 : Nat := (Nat.lor 0x200100000000480090000000001000000000101800300000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000200000000800580040000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020010000000000001000001000100000000010000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000120000020000480000058014000002000100001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000000004800000100000030000000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000002000000001004800400200200010000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000320000020000480000010000000003000100001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000100480040010010000001000003 (Nat.shiftLeft 0x320120000000480000010000000000000100101800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200200000000100480040010020000000000003 4096))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows568 : Nat := (Nat.lor 0x320100020000480010058004001002000100101800300000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200004800100580040010020001001018003000000000000000000000000000000000000000000000000000000000000000000000000000000000000032010002000048001005800400100200010010180030000000000000000000000000000000000000000000000000000000000000000000000000000000000000320100020000480010058004001002000100101800300000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200004800100580040010020001001018003000000000000000000000000000000000000000000000000000000000000000000000000000000000000032010002000048001005800400100200010010180030000000000000000000000000000000000000000000000000000000000000000000000000000000000000320100020000480010058004001002000100101800300000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200004800100580040010020001001018003 (Nat.shiftLeft 0x320100020000480010058004001002000100101800300000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200004800100580040010020001001018003 4096))
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices568 : sheets568 = boundedSlice 512 356 10 sheetTable ∧
    shadows568 = boundedSlice 512 356 10 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt568 (i : Nat) (hi : i < 10) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets568) (lane 512 i shadows568) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 356 10 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices568.1 slices568.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 568. -/
noncomputable def cert568 : AffineMaskCertificate := {
 beta := 0x3201000200004800100580040010020001001018003
 sectionColumns := [(28,0x4800000000000000000000000018003),(33,0x1),(34,0x4800000000000000000000000018001),(58,0x800000000000000000000000000000),(63,0x8001),(64,0x4000000000000000000000000008001),(81,0x1000000),(105,0x1000000000),(106,0x1000200000000000500000000020000001000000),(107,0x1000000000000000500000000020000001000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(154,0x200000000004800100000000000000000000018003),(155,0x4800100000000000000000000018003),(159,0x40000000000000000000),(160,0x200000000004800100080000010000000000018003),(161,0x1200000000004800100080000010000001000018003)]
 kernelColumns := [(0,0x3201000200004800100580040010020001001018003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x10000000000000,[0,1]),(0x20000000000000000,[2,3]),(0x100000000000000000000,[4,5]),(0x800000000000000000000000000,[6,7]),(0x200000000000000000000000000000000000000,[8,9])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked568 : (cert568).checkIndexedBoundary 180 512 10 sheets568 shadows568 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1bd800364800004800000090000090006c000093f = reconX FiberData.topRColumns (cert568).beta := AffineSearchData.rhsChecked568.symm
  have h : (cert568).checkIndexedBoundaryCached 180 512 10 sheets568 shadows568 0x1bd800364800004800000090000090006c000093f DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 569. -/
noncomputable def sheets569 : Nat := 0x2001000000004800d80000000000000000001018002000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000002000000008005000400000200010000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000200100000000000058000010000000000000100000200000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000200004800000500140000020001000018004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows569 : Nat := 0x3201000200004800580500040000020001001018006000000000000000000000000000000000000000000000000000000000000000000000000000000000000032010002000048005805000400000200010010180060000000000000000000000000000000000000000000000000000000000000000000000000000000000000320100020000480058050004000002000100101800600000000000000000000000000000000000000000000000000000000000000000000000000000000000003201000200004800580500040000020001001018006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices569 : sheets569 = boundedSlice 512 366 4 sheetTable ∧
    shadows569 = boundedSlice 512 366 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt569 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets569) (lane 512 i shadows569) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 366 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices569.1 slices569.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 569. -/
noncomputable def cert569 : AffineMaskCertificate := {
 beta := 0x3201000200004800580500040000020001001018006
 sectionColumns := [(33,0x4800000000000000000000000018002),(34,0x2),(35,0x4),(58,0x800000000000000000000000000000),(63,0x4800000000000000000000000010002),(64,0x800000000000000000000000010002),(81,0x1000000),(99,0x200000000000000180000000000000000000000000),(105,0x200000000000000180000000000000001000000000),(106,0x1000200000000000500000000020000001000000),(107,0x1000000000000000500000000020000001000000),(131,0x100000000000000000000000),(136,0x400000000000000000000000),(137,0x1000000000000000400000000000000001000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x40000000000000000000),(160,0x4800400000000000000000000018006),(161,0x1200000000004800580000000000000001000018006)]
 kernelColumns := [(0,0x3201000200004800580500040000020001001018006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x100000000000000000000,[0,1]),(0x800000000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked569 : (cert569).checkIndexedBoundary 180 512 4 sheets569 shadows569 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1bd80036000000480000009000009000fe4000936 = reconX FiberData.topRColumns (cert569).beta := AffineSearchData.rhsChecked569.symm
  have h : (cert569).checkIndexedBoundaryCached 180 512 4 sheets569 shadows569 0x1bd80036000000480000009000009000fe4000936 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 570. -/
noncomputable def sheets570 : Nat := 0x34000000000024006c000010001000000200000800100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000400280000020008000000020002000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000000002c0240000010008002000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000010004000000024000000c0100020000000000008002000000000000000000000000000000000000000000000000000000000000000000000000000000000000034000000000000002c0000180010000002000020001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000024000002800800200080000000080020000000000000000000000000000000000000000000000000000000000000000000000000000000000000340000000000240024008010000000000200000800400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000080200000030008000000020007
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows570 : Nat := 0x34004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000024002c0280100030008002000028003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices570 : sheets570 = boundedSlice 512 370 8 sheetTable ∧
    shadows570 = boundedSlice 512 370 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt570 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets570) (lane 512 i shadows570) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 370 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices570.1 slices570.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 570. -/
noncomputable def cert570 : AffineMaskCertificate := {
 beta := 0x34004000000024002c0280100030008002000028003
 sectionColumns := [(33,0x1),(34,0x2),(35,0x2400000000000000000000000028001),(59,0x400000000000000000000000000000),(63,0x8001),(65,0x2000000000000000000000000008001),(100,0x14004000000000000c0280000030008000000000000),(105,0x1000000000000000080080100010000000000000000),(106,0x14004000000000000c0280000030008002000000000),(129,0x1000000000000000080280100010008000000000000),(130,0x80000000000000000000000),(131,0x1000400000000000080280100010008000000000000),(135,0x200000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x1000400000000000080280000030008000000000000),(159,0x2400200000000000000000000028003),(160,0x80080000010000000000000000),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x34004000000024002c0280100030008002000028003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4,[0,1]),(0x80000000000000000000,[2,3]),(0x40000000000000000000000,[4,5]),(0x400000000000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked570 : (cert570).checkIndexedBoundary 180 512 8 sheets570 shadows570 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x369000004800002400000120249000006d2000dbf = reconX FiberData.topRColumns (cert570).beta := AffineSearchData.rhsChecked570.symm
  have h : (cert570).checkIndexedBoundaryCached 180 512 8 sheets570 shadows570 0x369000004800002400000120249000006d2000dbf DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 571. -/
noncomputable def sheets571 : Nat := 0x340000000000240024018010000000000200000800400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000980200000010008000000020004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows571 : Nat := 0x3400400000002400bc038010001000800200002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000003400400000002400bc0380100010008002000028000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices571 : sheets571 = boundedSlice 512 378 2 sheetTable ∧
    shadows571 = boundedSlice 512 378 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt571 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets571) (lane 512 i shadows571) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 378 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices571.1 slices571.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 571. -/
noncomputable def cert571 : AffineMaskCertificate := {
 beta := 0x3400400000002400bc0380100010008002000028000
 sectionColumns := [(34,0x800000100000000000000000000),(35,0x2400000000000000000000000028000),(59,0x400000000000000000000000000000),(63,0x8000),(65,0x2000000000000000000000000008000),(76,0x1000400000000000080380100010008000000000000),(100,0x400000000000000140000000000000000000000000),(105,0x1000000000000000080080100010000000000000000),(106,0x14004000000000001c0380100010008002000000000),(129,0x1000000000000000080280100010008000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x2400a00000100000000000000028000),(160,0x80080000010000000000000000),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x3400400000002400bc0380100010008002000028000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked571 : (cert571).checkIndexedBoundary 180 512 2 sheets571 shadows571 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x36900000d800002400000120249000006d2000da4 = reconX FiberData.topRColumns (cert571).beta := AffineSearchData.rhsChecked571.symm
  have h : (cert571).checkIndexedBoundaryCached 180 512 2 sheets571 shadows571 0x36900000d800002400000120249000006d2000da4 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 572. -/
noncomputable def sheets572 : Nat := 0x340000000000480024018008000000000200001800400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000580200000010008000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000034000000000048006c010008001000000200001800100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000100280000000008000000000001
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows572 : Nat := 0x34004000000048007c0380080010008002000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000048007c0380080010008002000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000048007c0380080010008002000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034004000000048007c0380080010008002000018000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices572 : sheets572 = boundedSlice 512 380 4 sheetTable ∧
    shadows572 = boundedSlice 512 380 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt572 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets572) (lane 512 i shadows572) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 380 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices572.1 slices572.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 572. -/
noncomputable def cert572 : AffineMaskCertificate := {
 beta := 0x34004000000048007c0380080010008002000018000
 sectionColumns := [(29,0x80080080010000000000000000),(34,0x4800000000000000000000000018000),(35,0x400000080000000000000000000),(58,0x800000000000000000000000000000),(63,0x8000),(64,0x4000000000000000000000000008000),(100,0x4000000000000001c0080080010000000000000000),(105,0x400000000000000300000000008000000000000),(106,0x4000000000000001c0080080010000002000000000),(129,0x400000000000000100000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(153,0xc0080080010000000000000000),(154,0x80080010000000000000000),(155,0x100000000000000000000000000),(159,0x4800600000080000000000000018000),(160,0x80000000000000000000),(161,0x1000400000000000000300080000008000000000000)]
 kernelColumns := [(0,0x34004000000048007c0380080010008002000018000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x1,[0,1]),(0x4,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked572 : (cert572).checkIndexedBoundary 180 512 4 sheets572 shadows572 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x900000d80000240000012000000000252000da4 = reconX FiberData.topRColumns (cert572).beta := AffineSearchData.rhsChecked572.symm
  have h : (cert572).checkIndexedBoundaryCached 180 512 4 sheets572 shadows572 0x900000d80000240000012000000000252000da4 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 573. -/
noncomputable def sheets573 : Nat := 0x3400000000006c0024018000000000000200001000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000180200000010008000000020004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows573 : Nat := 0x3400400000006c003c038000001000800200003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003400400000006c003c0380000010008002000030000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices573 : sheets573 = boundedSlice 512 384 2 sheetTable ∧
    shadows573 = boundedSlice 512 384 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt573 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets573) (lane 512 i shadows573) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 384 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices573.1 slices573.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 573. -/
noncomputable def cert573 : AffineMaskCertificate := {
 beta := 0x3400400000006c003c0380000010008002000030000
 sectionColumns := [(35,0x6c00000000000000000000000030000),(58,0x800000000000000000000000000000),(59,0x400000000000000000000000000000),(63,0x4800000000000000000000000010000),(64,0x800000000000000000000000010000),(65,0x6800000000000000000000000010000),(100,0x400000000000000140000000000000000000000000),(105,0x400000000000000300000000008000000000000),(106,0x400000000000000140000000000000002000000000),(129,0x400000000000000100000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x6c00200000000000000000000030000),(160,0x80080000010000000000000000),(161,0x1000400000000000080380000010008000000000000)]
 kernelColumns := [(0,0x3400400000006c003c0380000010008002000030000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked573 : (cert573).checkIndexedBoundary 180 512 2 sheets573 shadows573 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12900000d80000240000012024900000012000da4 = reconX FiberData.topRColumns (cert573).beta := AffineSearchData.rhsChecked573.symm
  have h : (cert573).checkIndexedBoundaryCached 180 512 2 sheets573 shadows573 0x12900000d80000240000012024900000012000da4 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 574. -/
noncomputable def sheets574 : Nat := 0x3400000000006c0004010000000000000200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000001200500200040000008000000020005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows574 : Nat := 0x3400400000007e0054030004000000800200000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000003400400000007e00540300040000008002000000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices574 : sheets574 = boundedSlice 512 386 2 sheetTable ∧
    shadows574 = boundedSlice 512 386 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt574 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets574) (lane 512 i shadows574) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 386 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices574.1 slices574.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 574. -/
noncomputable def cert574 : AffineMaskCertificate := {
 beta := 0x3400400000007e00540300040000008002000000005
 sectionColumns := [(5,0xe00000000000000000000000000000),(11,0x7000000000000000000000000000000),(33,0x1),(35,0xe00000000000000000000000000004),(58,0x600000000000000000000000000000),(59,0x400000000000000000000000000000),(64,0x3000000000000000000000000000000),(65,0x2000000000000000000000000000000),(100,0x400000000000000140000000000000000000000000),(105,0x400000007000000300000000008000000000000),(106,0x400000000000000140000000000000002000000000),(129,0x400000000000000100000000000000000000000),(131,0x100000000000000000000000),(135,0x7000000200000000000000000000000),(153,0x40000000000000000000000000),(155,0x100000000000000000000000000),(159,0x40000000000000000000),(160,0xe00400000000000000000000000005),(161,0x1000400000007e00400300000000008000000000005)]
 kernelColumns := [(0,0x3400400000007e00540300040000008002000000005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x20000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked574 : (cert574).checkIndexedBoundary 180 512 2 sheets574 shadows574 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1b900000900000240000012012480000936000dad = reconX FiberData.topRColumns (cert574).beta := AffineSearchData.rhsChecked574.symm
  have h : (cert574).checkIndexedBoundaryCached 180 512 2 sheets574 shadows574 0x1b900000900000240000012012480000936000dad DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 575. -/
noncomputable def sheets575 : Nat := 0x3400000000000000688000030011000003000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000000000000b00000100010000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000340000000000000020808003000100000300000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000480030000000001000000000007
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows575 : Nat := 0x34006000000000006880b0030001001003000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034006000000000006880b0030001001003000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034006000000000006880b0030001001003000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000034006000000000006880b0030001001003000000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices575 : sheets575 = boundedSlice 512 388 4 sheetTable ∧
    shadows575 = boundedSlice 512 388 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt575 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets575) (lane 512 i shadows575) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 388 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices575.1 slices575.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 575. -/
noncomputable def cert575 : AffineMaskCertificate := {
 beta := 0x34006000000000006880b0030001001003000000003
 sectionColumns := [(29,0x80010010000000000000000000),(33,0x1),(34,0x2),(100,0x4006000000000000880b0030001001000000000000),(105,0x1000000000),(106,0x4006000000000000880b0030001001002000000000),(123,0x600000000000000080000000001000000000000),(129,0x600000000000000080000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(147,0x8000000000000000000000000),(153,0x600000000000008080000001001000000000000),(154,0x10010000000000000000000),(155,0x80030030000000000000000000),(159,0x200000000000000000000000002),(160,0x400000000000000000000000001),(161,0x1000000000000000400000000000000001000000001),(178,0x10000000000000000000000),(179,0x80030010000000000000000000)]
 kernelColumns := [(0,0x34006000000000006880b0030001001003000000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4,[0,1]),(0x10000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked575 : (cert575).checkIndexedBoundary 180 512 4 sheets575 shadows575 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0xd8001248000048900000900001b0000000004a4d8003f = reconX FiberData.topRColumns (cert575).beta := AffineSearchData.rhsChecked575.symm
  have h : (cert575).checkIndexedBoundaryCached 180 512 4 sheets575 shadows575 0xd8001248000048900000900001b0000000004a4d8003f DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 576. -/
noncomputable def sheets576 : Nat := 0x340000040000000024018018000002000200000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000d80200000010000000002000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000034000004000000006c010018001002000200000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000900280000000000000002000001
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows576 : Nat := 0x3402000400000000fc038018001002000200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003402000400000000fc038018001002000200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003402000400000000fc038018001002000200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003402000400000000fc0380180010020002002000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices576 : sheets576 = boundedSlice 512 392 4 sheetTable ∧
    shadows576 = boundedSlice 512 392 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt576 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets576) (lane 512 i shadows576) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 392 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices576.1 slices576.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 576. -/
noncomputable def cert576 : AffineMaskCertificate := {
 beta := 0x3402000400000000fc0380180010020002002000000
 sectionColumns := [(29,0x80080080010000000000000000),(34,0x800000100000000000000000000),(35,0x400000080000000000000000000),(76,0x1002000400000000000300180000020000002000000),(82,0x1002000400000000000300180000020000000000000),(100,0x4000000000000001c0080080010000000000000000),(105,0x1000000000000000000000180000000000000000000),(106,0x14020004000000001c0380100010020002002000000),(107,0x1000000400000000000000180000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(137,0x1000000400000000000100180000020000000000000),(153,0xc0080080010000000000000000),(154,0x80080010000000000000000),(155,0x100000000000000000000000000),(159,0xe00000180000000000000000000),(160,0x80000000000000000000),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x3402000400000000fc0380180010020002002000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x1,[0,1]),(0x4,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked576 : (cert576).checkIndexedBoundary 180 512 4 sheets576 shadows576 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x24900024480000000000012000012000492000da4 = reconX FiberData.topRColumns (cert576).beta := AffineSearchData.rhsChecked576.symm
  have h : (cert576).checkIndexedBoundaryCached 180 512 4 sheets576 shadows576 0x24900024480000000000012000012000492000da4 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 577. -/
noncomputable def sheets577 : Nat := 0x24010000000000006c0000000020000002001000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000012004002000000000000c0000020030001000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000002000000006c0000000010030003000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014000000000000000c0000010000000001000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000002000000000000c0000008030003000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014000000000006c00000000080000000010000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000360000020000000024008000000003000300000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000001400000000000480040000000000000001000007
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows577 : Nat := 0x36014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036014002000000006c00c0000000030003001000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices577 : sheets577 = boundedSlice 512 396 8 sheetTable ∧
    shadows577 = boundedSlice 512 396 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt577 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets577) (lane 512 i shadows577) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 396 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices577.1 slices577.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 577. -/
noncomputable def cert577 : AffineMaskCertificate := {
 beta := 0x36014002000000006c00c0000000030003001000003
 sectionColumns := [(33,0x1),(34,0x2),(76,0x14002000000000000c0000000030000001000000),(81,0x1000000),(100,0x6000000000000000c0000000000000000000000000),(105,0x1000000000),(106,0x6014002000000000c00c0000000030002001000000),(107,0x6014000000000000c00c0000000030002001000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x1000200000000000080000000030000001000000),(136,0x6014002000000000c0040000000020002001000000),(137,0x6004002000000000c0040000000020002000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x200000000000000080000000000000000000000000),(159,0x200000000000000000000000002),(160,0x400000000000000000000000001),(161,0x1000000000000000400000000000000001000000001)]
 kernelColumns := [(0,0x36014002000000006c00c0000000030003001000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4,[0,1]),(0x8000000000000000,[2,3]),(0x10000000000000000,[4,5]),(0x20000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked577 : (cert577).checkIndexedBoundary 180 512 8 sheets577 shadows577 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1248003690000000000001b000009000492000009 = reconX FiberData.topRColumns (cert577).beta := AffineSearchData.rhsChecked577.symm
  have h : (cert577).checkIndexedBoundaryCached 180 512 8 sheets577 shadows577 0x1248003690000000000001b000009000492000009 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 578. -/
noncomputable def sheets578 : Nat := 0x24002004000000006c0000000020020002000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000012020000000000000000c0000020008001002000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000004000000006c0000000010020003000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022000000000000000c0000010008000002000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000036000004000000000000c0000008020003000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022000000000006c00000000080080000020000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000360000040000000024008000000002000300000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000480040000000008000002000007
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows578 : Nat := 0x36022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000036022004000000006c00c0000000028003002000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices578 : sheets578 = boundedSlice 512 404 8 sheetTable ∧
    shadows578 = boundedSlice 512 404 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt578 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets578) (lane 512 i shadows578) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 404 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices578.1 slices578.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 578. -/
noncomputable def cert578 : AffineMaskCertificate := {
 beta := 0x36022004000000006c00c0000000028003002000003
 sectionColumns := [(33,0x1),(34,0x2),(76,0x22004000000000000c0000000028000002000000),(82,0x22004000000000000c0000000028000000000000),(100,0x6000000000000000c0000000000000000000000000),(105,0x1000000000),(106,0x6022004000000000c00c0000000028002002000000),(107,0x400000000000000000000000001000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x200000000000000080000000000000000000000),(135,0x40000000008001000000000),(137,0x200400000000000080000000020001000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x200000000000000080000000000000000000000000),(159,0x200000000000000000000000002),(160,0x400000000000000000000000001),(161,0x1000000000000000400000000000000001000000001)]
 kernelColumns := [(0,0x36022004000000006c00c0000000028003002000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x4,[0,1]),(0x8000000000000000,[2,3]),(0x10000000000000000,[4,5]),(0x20000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked578 : (cert578).checkIndexedBoundary 180 512 8 sheets578 shadows578 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12480024d8000024000001b000012000492000009 = reconX FiberData.topRColumns (cert578).beta := AffineSearchData.rhsChecked578.symm
  have h : (cert578).checkIndexedBoundaryCached 180 512 8 sheets578 shadows578 0x12480024d8000024000001b000012000492000009 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 579. -/
noncomputable def sheets579 : Nat := 0x38000000000000014c000008004000000400000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000d00080000038000000000032
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows579 : Nat := 0x38008000000000014c0d00000040038004000000033000000000000000000000000000000000000000000000000000000000000000000000000000000000000038008000000000014c0d00000040038004000000033
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices579 : sheets579 = boundedSlice 512 412 2 sheetTable ∧
    shadows579 = boundedSlice 512 412 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt579 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets579) (lane 512 i shadows579) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 412 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices579.1 slices579.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 579. -/
noncomputable def cert579 : AffineMaskCertificate := {
 beta := 0x38008000000000014c0d00000040038004000000033
 sectionColumns := [(33,0x1),(34,0x2),(40,0x12),(41,0x20),(77,0x8000000000000000c0900000000020004000000000),(101,0x8000000000000000c0000000000000000000000000),(107,0x900000000020000000000000),(129,0x8008000000000000c0d00000000030004000000000),(130,0x400000000010000000000000),(131,0x100000000000000000000000),(135,0x8008000000000000c0d00000000038004000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x8008000000000010c0d00000040038004000000032),(160,0x400000000000000000000000001),(161,0x1000000000000000400000000000000000000000001),(165,0x1000000000000000000000000032)]
 kernelColumns := [(0,0x38008000000000014c0d00000040038004000000033)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked579 : (cert579).checkIndexedBoundary 180 512 2 sheets579 shadows579 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000009000000fc000002400000003691200049b = reconX FiberData.topRColumns (cert579).beta := AffineSearchData.rhsChecked579.symm
  have h : (cert579).checkIndexedBoundaryCached 180 512 2 sheets579 shadows579 0x12000009000000fc000002400000003691200049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 580. -/
noncomputable def sheets580 : Nat := 0x38000000000000022c000008008000000400000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000b00080000038000000000022
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows580 : Nat := 0x38008000000000022c0b0000008003800400000002b000000000000000000000000000000000000000000000000000000000000000000000000000000000000038008000000000022c0b0000008003800400000002b
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices580 : sheets580 = boundedSlice 512 414 2 sheetTable ∧
    shadows580 = boundedSlice 512 414 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt580 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets580) (lane 512 i shadows580) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 414 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices580.1 slices580.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 580. -/
noncomputable def cert580 : AffineMaskCertificate := {
 beta := 0x38008000000000022c0b0000008003800400000002b
 sectionColumns := [(33,0x1),(34,0x2),(39,0x9),(41,0x20),(77,0x8000000000000000c0900000000020004000000000),(101,0x8000000000000000c0000000000000000000000000),(107,0x900000000020000000000000),(129,0x200000000008000000000000),(130,0x8008000000000000c0b00000000028004000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x8008000000000000c0b00000000038004000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x200000000000000000000000002),(160,0x8008000000000020c0b00000080038004000000029),(161,0x18008000000000020c0b00000080038004000000029),(166,0x2000000000000000000000000029)]
 kernelColumns := [(0,0x38008000000000022c0b0000008003800400000002b)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked580 : (cert580).checkIndexedBoundary 180 512 2 sheets580 shadows580 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000012000000fc0000024000000024d920006db = reconX FiberData.topRColumns (cert580).beta := AffineSearchData.rhsChecked580.symm
  have h : (cert580).checkIndexedBoundaryCached 180 512 2 sheets580 shadows580 0x12000012000000fc0000024000000024d920006db DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 581. -/
noncomputable def sheets581 : Nat := 0x38000000000000030c00000800c000000400000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000900080000038000000000012
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows581 : Nat := 0x38008000000000030c09000000c003800400000001b000000000000000000000000000000000000000000000000000000000000000000000000000000000000038008000000000030c09000000c003800400000001b
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices581 : sheets581 = boundedSlice 512 416 2 sheetTable ∧
    shadows581 = boundedSlice 512 416 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt581 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets581) (lane 512 i shadows581) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 416 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices581.1 slices581.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 581. -/
noncomputable def cert581 : AffineMaskCertificate := {
 beta := 0x38008000000000030c09000000c003800400000001b
 sectionColumns := [(33,0x1),(34,0x2),(39,0x9),(40,0x12),(77,0x8000000000000000c0900000000020004000000000),(101,0x8000000000000000c0000000000000000000000000),(107,0x900000000020000000000000),(130,0x8008000000000000c0900000000020004000000000),(131,0x100000000000000000000000),(135,0x8000000000000),(136,0x8008000000000000c0900000000030004000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x1000000000040008000000000012),(160,0x8008000000000020c0900000080030004000000009),(161,0x18008000000000020c0900000080030004000000009),(165,0x1000000000000000000000000012),(166,0x2000000000000000000000000009)]
 kernelColumns := [(0,0x38008000000000030c09000000c003800400000001b)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked581 : (cert581).checkIndexedBoundary 180 512 2 sheets581 shadows581 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1200001b000000fc00000240000000120120006db = reconX FiberData.topRColumns (cert581).beta := AffineSearchData.rhsChecked581.symm
  have h : (cert581).checkIndexedBoundaryCached 180 512 2 sheets581 shadows581 0x1200001b000000fc00000240000000120120006db DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 582. -/
noncomputable def sheets582 : Nat := 0x380120000000000024000008001000000400100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000f80080000008000000000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows582 : Nat := 0x3801a00200000000240f8000001000800400100000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003801a00200000000240f80000010008004001000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices582 : sheets582 = boundedSlice 512 418 2 sheetTable ∧
    shadows582 = boundedSlice 512 418 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt582 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets582) (lane 512 i shadows582) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 418 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices582.1 slices582.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 582. -/
noncomputable def cert582 : AffineMaskCertificate := {
 beta := 0x3801a00200000000240f80000010008004001000006
 sectionColumns := [(34,0x2),(35,0x4),(51,0x1200000000000000d80000000000000001000000),(75,0x200000000000000180000000000000000000000),(81,0x1000000000000000c00000000000000000000000),(105,0x800000000000000280000000008000000000000),(106,0x1200200000000000d80000000000004001000000),(107,0x4000000000),(129,0x800000000000000080000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x800000000000000040000000000000000000000000),(159,0x200000000000000000000000006),(160,0x800000000000000040080000010000000000000000),(161,0x1800800000000000040200000010008000000000000)]
 kernelColumns := [(0,0x3801a00200000000240f80000010008004001000006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked582 : (cert582).checkIndexedBoundary 180 512 2 sheets582 shadows582 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000036900000fc0000024000009000db6000492 = reconX FiberData.topRColumns (cert582).beta := AffineSearchData.rhsChecked582.symm
  have h : (cert582).checkIndexedBoundaryCached 180 512 2 sheets582 shadows582 0x12000036900000fc0000024000009000db6000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 583. -/
noncomputable def sheets583 : Nat := 0x280120000000000048024010000800800400100000100000000000000000000000000000000000000000000000000000000000000000000000000000000000001000800200000000000d001000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000380120000000000048000008000800000400100000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000f40080000008000000000004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows583 : Nat := 0x3801a00200000000480f4000000800800400100000500000000000000000000000000000000000000000000000000000000000000000000000000000000000003801a00200000000480f4000000800800400100000500000000000000000000000000000000000000000000000000000000000000000000000000000000000003801a00200000000480f4000000800800400100000500000000000000000000000000000000000000000000000000000000000000000000000000000000000003801a00200000000480f40000008008004001000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices583 : sheets583 = boundedSlice 512 420 4 sheetTable ∧
    shadows583 = boundedSlice 512 420 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt583 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets583) (lane 512 i shadows583) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 420 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices583.1 slices583.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 583. -/
noncomputable def cert583 : AffineMaskCertificate := {
 beta := 0x3801a00200000000480f40000008008004001000005
 sectionColumns := [(33,0x1),(35,0x4),(75,0x1000000000000000c00000000000000001000000),(77,0x1a00000000000000d40000000000000001000000),(81,0x1000000000000000c00000000000000000000000),(105,0x240000000008000000000000),(106,0x1a00200000000000d40000000000004001000000),(107,0x1a00000000000000d40000000000004001000000),(129,0x40000000000000000000000),(130,0x1200000000000000d00000000000000001000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x800000000000000080000000000000000000000000),(154,0x80000000000000000000000000),(159,0x800000000000000080040000008000000000000000),(160,0x400000000000000000000000005),(161,0x1000000000000000400240000000008000000000005)]
 kernelColumns := [(0,0x3801a00200000000480f40000008008004001000005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked583 : (cert583).checkIndexedBoundary 180 512 4 sheets583 shadows583 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000036fc0000fc000002400000900092400049b = reconX FiberData.topRColumns (cert583).beta := AffineSearchData.rhsChecked583.symm
  have h : (cert583).checkIndexedBoundaryCached 180 512 4 sheets583 shadows583 0x12000036fc0000fc000002400000900092400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 584. -/
noncomputable def sheets584 : Nat := 0x38012000000000006c000008000000000400100000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800200000000000f00080000008000000000002
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows584 : Nat := 0x3801a002000000006c0f0000000000800400100000300000000000000000000000000000000000000000000000000000000000000000000000000000000000003801a002000000006c0f00000000008004001000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices584 : sheets584 = boundedSlice 512 424 2 sheetTable ∧
    shadows584 = boundedSlice 512 424 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt584 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets584) (lane 512 i shadows584) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 424 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices584.1 slices584.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 584. -/
noncomputable def cert584 : AffineMaskCertificate := {
 beta := 0x3801a002000000006c0f00000000008004001000003
 sectionColumns := [(33,0x1),(34,0x2),(75,0x1000000000000000c00000000000000001000000),(81,0x1000000000000000c00000000000000000000000),(101,0x8000000000000000c0000000000000000000000000),(105,0x1a00000000000000f00000000008000001000000),(106,0x8000002000000000c0000000000000004000000000),(107,0x8000000000000000c0000000000000004000000000),(129,0x1a00000000000000d00000000000000001000000),(130,0x1200000000000000d00000000000000001000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x200000000000000000000000002),(160,0x400000000000000000000000001),(161,0x1001a00000000000400f00000000008000001000001)]
 kernelColumns := [(0,0x3801a002000000006c0f00000000008004001000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked584 : (cert584).checkIndexedBoundary 180 512 2 sheets584 shadows584 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000036d80000fc000002400000900049200049b = reconX FiberData.topRColumns (cert584).beta := AffineSearchData.rhsChecked584.symm
  have h : (cert584).checkIndexedBoundaryCached 180 512 2 sheets584 shadows584 0x12000036d80000fc000002400000900049200049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 585. -/
noncomputable def sheets585 : Nat := 0x280240000000000048024010000800000400200000100000000000000000000000000000000000000000000000000000000000000000000000000000000000001000800400000000000d00100000010000000000004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows585 : Nat := 0x3802c00400000000480f4000000801000400200000500000000000000000000000000000000000000000000000000000000000000000000000000000000000003802c00400000000480f40000008010004002000005
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices585 : sheets585 = boundedSlice 512 426 2 sheetTable ∧
    shadows585 = boundedSlice 512 426 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt585 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets585) (lane 512 i shadows585) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 426 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices585.1 slices585.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 585. -/
noncomputable def cert585 : AffineMaskCertificate := {
 beta := 0x3802c00400000000480f40000008010004002000005
 sectionColumns := [(33,0x1),(35,0x4),(52,0x2400000000000000b40000000000000002000000),(76,0x400000000000000140000000000000000000000),(82,0x2000000000000000a00000000000000000000000),(105,0x2400400000000000b40000000000004002000000),(106,0x800000000000000440000000010000000000000),(107,0x4000000000),(129,0x40000000000000000000000),(130,0x800000000000000040000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x800000000000000080000000000000000000000000),(154,0x80000000000000000000000000),(159,0x800000000000000080040000008000000000000000),(160,0x400000000000000000000000005),(161,0x1002400400000000400b40000000000004002000005)]
 kernelColumns := [(0,0x3802c00400000000480f40000008010004002000005)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x100000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked585 : (cert585).checkIndexedBoundary 180 512 2 sheets585 shadows585 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000024b40000d8000002400001200092400049b = reconX FiberData.topRColumns (cert585).beta := AffineSearchData.rhsChecked585.symm
  have h : (cert585).checkIndexedBoundaryCached 180 512 2 sheets585 shadows585 0x12000024b40000d8000002400001200092400049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 586. -/
noncomputable def sheets586 : Nat := 0x380000080000000090000008003800000400000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000ec0080000020000004000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows586 : Nat := 0x3804000800000000900ec000003802000400400000300000000000000000000000000000000000000000000000000000000000000000000000000000000000003804000800000000900ec0000038020004004000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices586 : sheets586 = boundedSlice 512 428 2 sheetTable ∧
    shadows586 = boundedSlice 512 428 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt586 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets586) (lane 512 i shadows586) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 428 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices586.1 slices586.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 586. -/
noncomputable def cert586 : AffineMaskCertificate := {
 beta := 0x3804000800000000900ec0000038020004004000003
 sectionColumns := [(33,0x1),(34,0x2),(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(101,0x4000000000000900e00000020020004004000003),(106,0x800000000000000000000000000000000000),(107,0x900800000020020000000000003),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x900000000020000000000000003),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x1804000000000000100e80000030020004004000000),(154,0x1000000000000000800080000010000000000000003),(155,0x100000000000000000000000000),(159,0x1804000000000000100ec0000038020004004000000),(160,0x1000000000000000800000000000000000000000003),(161,0x800000000000000000000000003)]
 kernelColumns := [(0,0x3804000800000000900ec0000038020004004000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked586 : (cert586).checkIndexedBoundary 180 512 2 sheets586 shadows586 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000000fc0000900000024000024000000000489 = reconX FiberData.topRColumns (cert586).beta := AffineSearchData.rhsChecked586.symm
  have h : (cert586).checkIndexedBoundaryCached 180 512 2 sheets586 shadows586 0x12000000fc0000900000024000024000000000489 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 587. -/
noncomputable def sheets587 : Nat := 0x3800000800000000d8000008002800000400000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000e40080000020000004000004
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows587 : Nat := 0x3804000800000000d80e4000002802000400400000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003804000800000000d80e40000028020004004000006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices587 : sheets587 = boundedSlice 512 430 2 sheetTable ∧
    shadows587 = boundedSlice 512 430 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt587 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets587) (lane 512 i shadows587) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 430 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices587.1 slices587.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 587. -/
noncomputable def cert587 : AffineMaskCertificate := {
 beta := 0x3804000800000000d80e40000028020004004000006
 sectionColumns := [(34,0x2),(35,0x4),(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(101,0x4000000000000900e00000020020004004000002),(105,0x1000000000000000c00000000000000000000000006),(106,0x1000000800000000c00000000000000000000000006),(107,0x900800000020020000000000002),(129,0x40000000000000000000000),(131,0x900000000020000000000000002),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x804000000000000980e00000020020004004000002),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0x804000000000000980e40000028020004004000002),(160,0x400000000000000000000000004),(161,0x800000000000000000000000002)]
 kernelColumns := [(0,0x3804000800000000d80e40000028020004004000006)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked587 : (cert587).checkIndexedBoundary 180 512 2 sheets587 shadows587 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000000b40000900000024000024000924000480 = reconX FiberData.topRColumns (cert587).beta := AffineSearchData.rhsChecked587.symm
  have h : (cert587).checkIndexedBoundaryCached 180 512 2 sheets587 shadows587 0x12000000b40000900000024000024000924000480 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 588. -/
noncomputable def sheets588 : Nat := 0x380000080000000104000008005000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000d80080000020000004000036
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows588 : Nat := 0x3804000800000001040d8000005002000400400003600000000000000000000000000000000000000000000000000000000000000000000000000000000000003804000800000001040d80000050020004004000036
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices588 : sheets588 = boundedSlice 512 432 2 sheetTable ∧
    shadows588 = boundedSlice 512 432 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt588 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets588) (lane 512 i shadows588) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 432 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices588.1 slices588.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 588. -/
noncomputable def cert588 : AffineMaskCertificate := {
 beta := 0x3804000800000001040d80000050020004004000036
 sectionColumns := [(34,0x2),(35,0x4),(40,0x12),(41,0x24),(83,0x4000000),(101,0x900000000020004000000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x4000000000000000400000000000000004000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x800000000000000040900000000020004000000000),(159,0x4000000000001000400000040000000004000036),(160,0x800000000000000040980000010020004000000000),(161,0x1800000000000000040980000010020004000000000),(165,0x1000000000000000000000000036)]
 kernelColumns := [(0,0x3804000800000001040d80000050020004004000036)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked588 : (cert588).checkIndexedBoundary 180 512 2 sheets588 shadows588 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000009480000900000024000024036036000492 = reconX FiberData.topRColumns (cert588).beta := AffineSearchData.rhsChecked588.symm
  have h : (cert588).checkIndexedBoundaryCached 180 512 2 sheets588 shadows588 0x12000009480000900000024000024036036000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 589. -/
noncomputable def sheets589 : Nat := 0x380000080000000120000008005800000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000dc0080000020000004000030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows589 : Nat := 0x3804000800000001200dc000005802000400400003000000000000000000000000000000000000000000000000000000000000000000000000000000000000003804000800000001200dc0000058020004004000030
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices589 : sheets589 = boundedSlice 512 434 2 sheetTable ∧
    shadows589 = boundedSlice 512 434 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt589 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets589) (lane 512 i shadows589) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 434 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices589.1 slices589.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 589. -/
noncomputable def cert589 : AffineMaskCertificate := {
 beta := 0x3804000800000001200dc0000058020004004000030
 sectionColumns := [(40,0x10),(41,0x20),(77,0x4000000000001200400000040000000004000030),(83,0x4000000000001200400000040000000000000030),(101,0x4000000000001200d00000040020004004000030),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x1200000000040000000000000030),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x200040000008000000000000000),(154,0x804000000000001000d40000048020004004000030),(159,0x200000000000000000000000000),(160,0x804000000000001000dc0000058020004004000030),(161,0x1804000000000001000dc0000058020004004000030),(165,0x1000000000000000000000000030)]
 kernelColumns := [(0,0x3804000800000001200dc0000058020004004000030)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked589 : (cert589).checkIndexedBoundary 180 512 2 sheets589 shadows589 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000096c0000900000024000024036d80000492 = reconX FiberData.topRColumns (cert589).beta := AffineSearchData.rhsChecked589.symm
  have h : (cert589).checkIndexedBoundaryCached 180 512 2 sheets589 shadows589 0x120000096c0000900000024000024036d80000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 590. -/
noncomputable def sheets590 : Nat := 0x38000008000000014c000008004000000400000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000d00080000020000004000032
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows590 : Nat := 0x38040008000000014c0d00000040020004004000033000000000000000000000000000000000000000000000000000000000000000000000000000000000000038040008000000014c0d00000040020004004000033
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices590 : sheets590 = boundedSlice 512 436 2 sheetTable ∧
    shadows590 = boundedSlice 512 436 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt590 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets590) (lane 512 i shadows590) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 436 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices590.1 slices590.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 590. -/
noncomputable def cert590 : AffineMaskCertificate := {
 beta := 0x38040008000000014c0d00000040020004004000033
 sectionColumns := [(33,0x1),(34,0x2),(40,0x12),(41,0x20),(77,0x8000000000000000c0900000000020004000000000),(83,0x8000000000000000c0900000000020004004000000),(101,0x8000000000000000c0000000000000000000000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(131,0x100000000000000000000000),(135,0x8040000000000000c0d00000000020004004000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x8040000000000010c0d00000040020004004000032),(160,0x400000000000000000000000001),(161,0x1000000000000000400000000000000000000000001),(165,0x1000000000000000000000000032)]
 kernelColumns := [(0,0x38040008000000014c0d00000040020004004000033)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked590 : (cert590).checkIndexedBoundary 180 512 2 sheets590 shadows590 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1200000900000090000002400002403691200049b = reconX FiberData.topRColumns (cert590).beta := AffineSearchData.rhsChecked590.symm
  have h : (cert590).checkIndexedBoundaryCached 180 512 2 sheets590 shadows590 0x1200000900000090000002400002403691200049b DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 591. -/
noncomputable def sheets591 : Nat := 0x380000080000000208000008008800000400000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000b40080000020000004000024
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows591 : Nat := 0x3804000800000002080b4000008802000400400002d00000000000000000000000000000000000000000000000000000000000000000000000000000000000003804000800000002080b4000008802000400400002d
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices591 : sheets591 = boundedSlice 512 438 2 sheetTable ∧
    shadows591 = boundedSlice 512 438 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt591 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets591) (lane 512 i shadows591) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 438 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices591.1 slices591.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 591. -/
noncomputable def cert591 : AffineMaskCertificate := {
 beta := 0x3804000800000002080b4000008802000400400002d
 sectionColumns := [(33,0x1),(35,0x4),(39,0x9),(41,0x24),(83,0x4000000),(101,0x900000000020004000000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x4000000000000000200000000000000004000000),(137,0x800000000000000000000000),(153,0x800000000000000080900000000020004000000000),(154,0x80000000000000000000000000),(159,0x800000000000000080940000008020004000000000),(160,0x400000000000200020000008000000000400002d),(161,0x100400000000000200020000008000000000400002d),(166,0x200000000000000000000000002d)]
 kernelColumns := [(0,0x3804000800000002080b4000008802000400400002d)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked591 : (cert591).checkIndexedBoundary 180 512 2 sheets591 shadows591 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000122400009000000240000240240240006db = reconX FiberData.topRColumns (cert591).beta := AffineSearchData.rhsChecked591.symm
  have h : (cert591).checkIndexedBoundaryCached 180 512 2 sheets591 shadows591 0x120000122400009000000240000240240240006db DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 592. -/
noncomputable def sheets592 : Nat := 0x38000008000000022c000008008000000400000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000b00080000020000004000022
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows592 : Nat := 0x38040008000000022c0b0000008002000400400002b000000000000000000000000000000000000000000000000000000000000000000000000000000000000038040008000000022c0b0000008002000400400002b
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices592 : sheets592 = boundedSlice 512 440 2 sheetTable ∧
    shadows592 = boundedSlice 512 440 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt592 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets592) (lane 512 i shadows592) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 440 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices592.1 slices592.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 592. -/
noncomputable def cert592 : AffineMaskCertificate := {
 beta := 0x38040008000000022c0b0000008002000400400002b
 sectionColumns := [(33,0x1),(34,0x2),(39,0x9),(41,0x20),(77,0x8000000000000000c0900000000020004000000000),(83,0x8000000000000000c0900000000020004004000000),(101,0x8000000000000000c0000000000000000000000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x8040000000000000c0b00000000020004004000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x200000000000000000000000002),(160,0x8040000000000020c0b00000080020004004000029),(161,0x18040000000000020c0b00000080020004004000029),(166,0x2000000000000000000000000029)]
 kernelColumns := [(0,0x38040008000000022c0b0000008002000400400002b)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked592 : (cert592).checkIndexedBoundary 180 512 2 sheets592 shadows592 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000012000000900000024000024024d920006db = reconX FiberData.topRColumns (cert592).beta := AffineSearchData.rhsChecked592.symm
  have h : (cert592).checkIndexedBoundaryCached 180 512 2 sheets592 shadows592 0x12000012000000900000024000024024d920006db DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 593. -/
noncomputable def sheets593 : Nat := 0x380000080000000240000008009800000400000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000bc0080000020000004000020
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows593 : Nat := 0x3804000800000002400bc000009802000400400002800000000000000000000000000000000000000000000000000000000000000000000000000000000000003804000800000002400bc0000098020004004000028
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices593 : sheets593 = boundedSlice 512 442 2 sheetTable ∧
    shadows593 = boundedSlice 512 442 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt593 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets593) (lane 512 i shadows593) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 442 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices593.1 slices593.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 593. -/
noncomputable def cert593 : AffineMaskCertificate := {
 beta := 0x3804000800000002400bc0000098020004004000028
 sectionColumns := [(39,0x8),(41,0x20),(77,0x4000000000002400200000080000000004000028),(83,0x4000000000002400200000080000000000000028),(101,0x4000000000002400b00000080020004004000028),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x2400000000080000000000000028),(137,0x800000000000000000000000),(153,0x804000000000002000b80000090020004004000028),(154,0x400080000010000000000000000),(159,0x804000000000002000bc0000098020004004000028),(160,0x400000000000000000000000000),(161,0x1000000000000000400000000000000000000000000),(166,0x2000000000000000000000000028)]
 kernelColumns := [(0,0x3804000800000002400bc0000098020004004000028)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked593 : (cert593).checkIndexedBoundary 180 512 2 sheets593 shadows593 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000126c00009000000240000240249000006d2 = reconX FiberData.topRColumns (cert593).beta := AffineSearchData.rhsChecked593.symm
  have h : (cert593).checkIndexedBoundaryCached 180 512 2 sheets593 shadows593 0x120000126c00009000000240000240249000006d2 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 594. -/
noncomputable def sheets594 : Nat := 0x38000008000000030c00000800c000000400000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000900080000020000004000012
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows594 : Nat := 0x38040008000000030c09000000c002000400400001b000000000000000000000000000000000000000000000000000000000000000000000000000000000000038040008000000030c09000000c002000400400001b
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices594 : sheets594 = boundedSlice 512 444 2 sheetTable ∧
    shadows594 = boundedSlice 512 444 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt594 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets594) (lane 512 i shadows594) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 444 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices594.1 slices594.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 594. -/
noncomputable def cert594 : AffineMaskCertificate := {
 beta := 0x38040008000000030c09000000c002000400400001b
 sectionColumns := [(33,0x1),(34,0x2),(39,0x9),(40,0x12),(77,0x8000000000000000c0900000000020004000000000),(83,0x8000000000000000c0900000000020004004000000),(101,0x8000000000000000c0000000000000000000000000),(106,0x800000000000000000000000000000000000),(107,0x900000000020000000000000),(131,0x100000000000000000000000),(136,0x8040000000000000c0900000000020004004000000),(137,0x800000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(159,0x1000000000040000000000000012),(160,0x8040000000000020c0900000080020004004000009),(161,0x18040000000000020c0900000080020004004000009),(165,0x1000000000000000000000000012),(166,0x2000000000000000000000000009)]
 kernelColumns := [(0,0x38040008000000030c09000000c002000400400001b)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked594 : (cert594).checkIndexedBoundary 180 512 2 sheets594 shadows594 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x1200001b0000009000000240000240120120006db = reconX FiberData.topRColumns (cert594).beta := AffineSearchData.rhsChecked594.symm
  have h : (cert594).checkIndexedBoundaryCached 180 512 2 sheets594 shadows594 0x1200001b0000009000000240000240120120006db DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 595. -/
noncomputable def sheets595 : Nat := 0x3800000800000004800000080118000004000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000007c0080000020000004000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows595 : Nat := 0x38040008000000048007c0000118020004004000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000038040008000000048007c0000118020004004000018
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices595 : sheets595 = boundedSlice 512 446 2 sheetTable ∧
    shadows595 = boundedSlice 512 446 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt595 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets595) (lane 512 i shadows595) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 446 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices595.1 slices595.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 595. -/
noncomputable def cert595 : AffineMaskCertificate := {
 beta := 0x38040008000000048007c0000118020004004000018
 sectionColumns := [(39,0x8),(40,0x10),(77,0x4000000000000000600000000000000004000000),(83,0x4000000000000000600000000000000000000000),(101,0x4000000000004800700000100020004004000018),(106,0x800000000000000000000000000000000000),(107,0x4800100000100020000000000018),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x4800000000100000000000000018),(153,0x1804000000000004000780000110020004004000018),(154,0x1000000000000000800080000010000000000000000),(159,0x18040000000000040007c0000118020004004000018),(160,0x1000000000000000800000000000000000000000000),(161,0x800000000000000000000000000),(167,0x4000000000000000000000000018)]
 kernelColumns := [(0,0x38040008000000048007c0000118020004004000018)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked595 : (cert595).checkIndexedBoundary 180 512 2 sheets595 shadows595 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x120000246c0000900000024000024000000000252 = reconX FiberData.topRColumns (cert595).beta := AffineSearchData.rhsChecked595.symm
  have h : (cert595).checkIndexedBoundaryCached 180 512 2 sheets595 shadows595 0x120000246c0000900000024000024000000000252 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 596. -/
noncomputable def sheets596 : Nat := 0x380120080000000000000008001800000400100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000200000000000fc0080000010000004000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows596 : Nat := 0x3805200a00000000000fc000001801000400500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003805200a00000000000fc0000018010004005000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices596 : sheets596 = boundedSlice 512 448 2 sheetTable ∧
    shadows596 = boundedSlice 512 448 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt596 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets596) (lane 512 i shadows596) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 448 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices596.1 slices596.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 596. -/
noncomputable def cert596 : AffineMaskCertificate := {
 beta := 0x3805200a00000000000fc0000018010004005000000
 sectionColumns := [(51,0x1200000000000000d80000000000000001000000),(75,0x200000000000000180000000000000000000000),(77,0x4000000000000000600000000000000004000000),(81,0x1000000000000000c00000000000000000000000),(83,0x4000000000000000600000000000000000000000),(101,0x5200200000000000f00000000010004005000000),(105,0x800000000000480000000010000000000000),(106,0x480000000010000000000000),(107,0x1200200000000000900000000010000001000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(154,0x805200200000000000f00000000010004005000000),(159,0x40000008000000000000000),(160,0x805200200000000000f80000010010004005000000),(161,0x1805200a00000000000b00000010000004005000000)]
 kernelColumns := [(0,0x3805200a00000000000fc0000018010004005000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked596 : (cert596).checkIndexedBoundary 180 512 2 sheets596 shadows596 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000036b4000090000002400002d000000000492 = reconX FiberData.topRColumns (cert596).beta := AffineSearchData.rhsChecked596.symm
  have h : (cert596).checkIndexedBoundaryCached 180 512 2 sheets596 shadows596 0x12000036b4000090000002400002d000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 597. -/
noncomputable def sheets597 : Nat := 0x280240080000000000024010001800000400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001004000400000000000d801000000080000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000380240080000000000000008001800800400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000400000000000fc0080000000000004000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows597 : Nat := 0x3806400c00000000000fc000001800800400600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003806400c00000000000fc000001800800400600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003806400c00000000000fc000001800800400600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003806400c00000000000fc0000018008004006000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices597 : sheets597 = boundedSlice 512 450 4 sheetTable ∧
    shadows597 = boundedSlice 512 450 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt597 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets597) (lane 512 i shadows597) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 450 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices597.1 slices597.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 597. -/
noncomputable def cert597 : AffineMaskCertificate := {
 beta := 0x3806400c00000000000fc0000018008004006000000
 sectionColumns := [(52,0x2400000000000000b40000000000000002000000),(76,0x400000000000000140000000000000000000000),(77,0x4000000000000000600000000000000004000000),(82,0x2000000000000000a00000000000000000000000),(83,0x4000000000000000600000000000000000000000),(101,0x6400400000000000f00000000008004006000000),(105,0x240000000008000000000000),(106,0x800000000000240000000008000000000000),(107,0x2400400000000000900000000008000002000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(154,0x806400400000000000f00000000008004006000000),(159,0x40000008000000000000000),(160,0x806400400000000000f80000010008004006000000),(161,0x1806400400000000000dc0000010000004006000000)]
 kernelColumns := [(0,0x3806400c00000000000fc0000018008004006000000)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x80000000000000000000,[0,1]),(0x100000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked597 : (cert597).checkIndexedBoundary 180 512 4 sheets597 shadows597 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12000024fc0000b40000024000036000000000492 = reconX FiberData.topRColumns (cert597).beta := AffineSearchData.rhsChecked597.symm
  have h : (cert597).checkIndexedBoundaryCached 180 512 4 sheets597 shadows597 0x12000024fc0000b40000024000036000000000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 598. -/
noncomputable def sheets598 : Nat := 0x39c00008e000002000000000000a00200080000090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000004000012001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c01008e000002000000000000900200000000090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900000000000000000004000011001000800000000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows598 : Nat := 0x39c01008e0000020000004000018003000800000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000039c01008e0000020000004000018003000800000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000039c01008e0000020000004000018003000800000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000039c01008e0000020000004000018003000800000900
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices598 : sheets598 = boundedSlice 512 454 4 sheetTable ∧
    shadows598 = boundedSlice 512 454 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt598 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets598) (lane 512 i shadows598) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 454 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices598.1 slices598.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 598. -/
noncomputable def cert598 : AffineMaskCertificate := {
 beta := 0x39c01008e0000020000004000018003000800000900
 sectionColumns := [(46,0x20000004000000000000000000000),(47,0x100),(53,0x900),(94,0x20000000000000000000000000000000000),(95,0x1c0000020000000000000000000000000000000000),(99,0x1c00000a0000020000004000000000000800000000),(100,0x1c0000060000000000000000000000000800000000),(101,0x1c0000020000000000000000000000000800000000),(106,0x800000000000000000000000000000000900),(124,0x100000000000000000000000000000000000000),(129,0x1c00000a0000020000004000000001000800000000),(130,0x1c0100060000000000000000000002000800000000),(148,0xc0000020000000000000000000000000000000000),(149,0x80000020000000000000000000000000000000000),(154,0x9c0000020000000000000000000000000800000000),(159,0x1c00000a0000020000004000008001000800000000),(160,0x800100040000000000000000010002000000000000),(161,0x1800100040000000000000000010002000000000000),(173,0x4000000000000000000000)]
 kernelColumns := [(0,0x39c01008e0000020000004000018003000800000900)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x1000000000000000,[0,1]),(0x2000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked598 : (cert598).checkIndexedBoundary 180 512 4 sheets598 shadows598 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x240120120006c0000009000000900000000000924000 = reconX FiberData.topRColumns (cert598).beta := AffineSearchData.rhsChecked598.symm
  have h : (cert598).checkIndexedBoundaryCached 180 512 4 sheets598 shadows598 0x240120120006c0000009000000900000000000924000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 599. -/
noncomputable def sheets599 : Nat := 0x7c00000400000000000800140010000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040028000000000009002400000000000000020000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000340080040000000000080014000800000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000802000000000000900240000018000004002000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows599 : Nat := 0x3c02800400000000900a4014001000000600200000300000000000000000000000000000000000000000000000000000000000000000000000000000000000003c02800400000000900a4014001000000600200000300000000000000000000000000000000000000000000000000000000000000000000000000000000000003c02800400000000900a4014001000000600200000300000000000000000000000000000000000000000000000000000000000000000000000000000000000003c02800400000000900a40140010000006002000003
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices599 : sheets599 = boundedSlice 512 458 4 sheetTable ∧
    shadows599 = boundedSlice 512 458 4 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt599 (i : Nat) (hi : i < 4) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets599) (lane 512 i shadows599) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 458 4 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices599.1 slices599.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 599. -/
noncomputable def cert599 : AffineMaskCertificate := {
 beta := 0x3c02800400000000900a40140010000006002000003
 sectionColumns := [(28,0x800000100000000000000000003),(33,0x1),(34,0x800000100000000000000000001),(76,0x2000000000000000a00000000000000002000000),(82,0x2000000000000000a00000000000000000000000),(100,0x1c00800400000000900040000010000004000000003),(105,0x400000000000000000000000004000000000),(106,0x1c02800400000000900a40000010000006002000003),(107,0x4000000000),(129,0x40000000000000000000000),(130,0x800000000000000040000000000000000000000),(135,0x200000000000000000000000),(137,0x800000000000000000000000),(153,0x1800800400000000000040100010000004000000000),(154,0x1000800400000000000040100010000004000000000),(155,0x900000100000000000000000003),(159,0x40000000000000000000),(160,0x1000000400000000000000100000000004000000000),(161,0x100000000000000000000)]
 kernelColumns := [(0,0x3c02800400000000900a40140010000006002000003)]
 decoderColumns := [(169,0x1)]
 dimension := 1
 seeds := [(0x8000000000000000,[0,1]),(0x4000000000000000000000000000000000000000000,[2,3])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked599 : (cert599).checkIndexedBoundary 180 512 4 sheets599 shadows599 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x3f900024480000900000036000012000000000dad = reconX FiberData.topRColumns (cert599).beta := AffineSearchData.rhsChecked599.symm
  have h : (cert599).checkIndexedBoundaryCached 180 512 4 sheets599 shadows599 0x3f900024480000900000036000012000000000dad DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 600. -/
noncomputable def sheets600 : Nat := 0x47c00000a000000000000000001a00400480000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440000020000000000000002002000000c00000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows600 : Nat := 0x47c04400a0020000000000000018006004800c00100000000000000000000000000000000000000000000000000000000000000000000000000000000000000047c04400a0020000000000000018006004800c00100
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices600 : sheets600 = boundedSlice 512 462 2 sheetTable ∧
    shadows600 = boundedSlice 512 462 2 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt600 (i : Nat) (hi : i < 2) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets600) (lane 512 i shadows600) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 462 2 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices600.1 slices600.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 600. -/
noncomputable def cert600 : AffineMaskCertificate := {
 beta := 0x47c04400a0020000000000000018006004800c00100
 sectionColumns := [(47,0x100),(70,0x20000000000000000000000000000000),(76,0x20000000000000000000000000400000),(77,0x800100),(94,0x20000000000000000000000000000000000),(95,0x1c0000020000000000000000000000000000000000),(99,0x1c00000a0000000000000000000000000800000000),(101,0x1c0000020000000000000000000000000800000000),(107,0x1c0000020000000000000000000000004800800100),(125,0x40000000000000000000000000000000000000),(129,0x1c0440020020000000000000000004000800400000),(130,0x2000000000000),(131,0x1c0040020000000000000000000004000800000000),(148,0xc0000020000000000000000000000000000000000),(149,0x80000020000000000000000000000000000000000),(154,0x7c00000a0000000000000000000000000800000000),(155,0x400000000000000000000000000000000000000000),(159,0x1c0440020020000000000000008004000800400000),(160,0x7c00000a0000000000000000010002000800000000)]
 kernelColumns := [(0,0x47c04400a0020000000000000018006004800c00100)]
 decoderColumns := [(170,0x1)]
 dimension := 1
 seeds := [(0x2000000000000000,[0,1])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked600 : (cert600).checkIndexedBoundary 180 512 2 sheets600 shadows600 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x492000ff6000012000024900000d80000024000 = reconX FiberData.topRColumns (cert600).beta := AffineSearchData.rhsChecked600.symm
  have h : (cert600).checkIndexedBoundaryCached 180 512 2 sheets600 shadows600 0x492000ff6000012000024900000d80000024000 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 601. -/
noncomputable def sheets601 : Nat := 0x4800120000000000fc000000002000060400010000200000000000000000000000000000000000000000000000000000000000000000000000000000000000004800000020000000fc0000000020000004000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009200000000000001c0000000000600000100002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000200000000001c0000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000048001200000000006c0100000000000604000100001000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000000200000006c0100000000000004000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009200000000009000c0000020000600000100001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000200000009000c0000020000000000000001
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows601 : Nat := 0x4800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c000002000060400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800920020000000fc01c0000020000604000100000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices601 : sheets601 = boundedSlice 512 464 8 sheetTable ∧
    shadows601 = boundedSlice 512 464 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt601 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets601) (lane 512 i shadows601) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 464 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices601.1 slices601.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 601. -/
noncomputable def cert601 : AffineMaskCertificate := {
 beta := 0x4800920020000000fc01c0000020000604000100000
 sectionColumns := [(34,0x900100000020000000000000000),(71,0x100000),(77,0x8000000000000000c0000000000000000000000),(94,0x20000000000000000000000000000000000),(101,0x8000000000000000c0000000000000000000000000),(107,0x8008000000000000c00c0000000000004000000000),(118,0x20000000000000000000000000000000000000),(123,0x200000000000),(124,0x20020000000000000000000000400000000000),(129,0x40000000000000000000000),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(153,0x40000000000000000000000000),(154,0x80000000000000000000000000),(155,0x100000000000000000000000000),(159,0xb00100000020000000000000000),(160,0x400000000000000000000000000),(161,0x100100000020000000000000000)]
 kernelColumns := [(0,0x120020000000000000000000000600000100000),(1,0x4800800000000000fc01c0000020000004000000000)]
 decoderColumns := [(152,0x1),(170,0x2)]
 dimension := 2
 seeds := [(0x1,[0,1,2,3]),(0x2,[4,5,6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked601 : (cert601).checkIndexedBoundary 180 512 8 sheets601 shadows601 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x9000000006c0024000000024492000012 = reconX FiberData.topRColumns (cert601).beta := AffineSearchData.rhsChecked601.symm
  have h : (cert601).checkIndexedBoundaryCached 180 512 8 sheets601 shadows601 0x9000000006c0024000000024492000012 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 602. -/
noncomputable def sheets602 : Nat := 0x40000000000208002002409000000080000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000001204800900100000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000000000208002000008800000000000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001204800b4008000002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000001204800240040000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000208002009008400000200000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000004a0024000000000800000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000021a000009008000000200000000d8000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows602 : Nat := 0x5000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e800000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000021a04a00b408000000280000000e8000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices602 : sheets602 = boundedSlice 512 472 8 sheetTable ∧
    shadows602 = boundedSlice 512 472 8 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt602 (i : Nat) (hi : i < 8) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets602) (lane 512 i shadows602) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 472 8 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices602.1 slices602.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 602. -/
noncomputable def cert602 : AffineMaskCertificate := {
 beta := 0x5000000000021a04a00b408000000280000000e8000
 sectionColumns := [(35,0x21a040000008000000000000000e8000),(40,0x4000000800000000000000000000),(58,0x800000000000000000000000000000),(59,0xa00000000000000000000000000000),(63,0x8000),(64,0x200040000008000000000000000c8000),(65,0x210040000008000000000000000c8000),(69,0x48000),(70,0x20000000000000000000000000048000),(105,0x240000000008000000000000),(107,0x900000000020000000000000),(129,0x40000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(137,0x800000000000000000000000),(159,0x21a042000008000000000000000e8000),(160,0x1000000000000000800240000000008000000000000),(161,0x800000000000000000000000000),(167,0x800000000000000000000)]
 kernelColumns := [(0,0x5000000000021a04a00b408000000280000000e8000)]
 decoderColumns := [(170,0x1)]
 dimension := 1
 seeds := [(0x10000,[0,1]),(0x40000000000000000000,[2,3]),(0x80000000000000000000,[4,5]),(0x100000000000000000000,[6,7])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked602 : (cert602).checkIndexedBoundary 180 512 8 sheets602 shadows602 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x936000000000000b40000000036d8001b6c0000db6 = reconX FiberData.topRColumns (cert602).beta := AffineSearchData.rhsChecked602.symm
  have h : (cert602).checkIndexedBoundaryCached 180 512 8 sheets602 shadows602 0x936000000000000b40000000036d8001b6c0000db6 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidate sheets of top fiber 603. -/
noncomputable def sheets603 : Nat := 0x600000000000024000020010800000800000000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000200d801000080300000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700000000000000020000008000800000000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240000f800880000380000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000024000068004800001800000000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200900040008020000000006000
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The shadow accompanying each candidate. -/
noncomputable def shadows603 : Nat := 0x7000000000000240200f8000800803800000000600600000000000000000000000000000000000000000000000000000000000000000000000000000000000007000000000000240200f8000800803800000000600600000000000000000000000000000000000000000000000000000000000000000000000000000000000007000000000000240200f8000800803800000000600600000000000000000000000000000000000000000000000000000000000000000000000000000000000007000000000000240200f8000800803800000000600600000000000000000000000000000000000000000000000000000000000000000000000000000000000007000000000000240200f8000800803800000000600600000000000000000000000000000000000000000000000000000000000000000000000000000000000007000000000000240200f80008008038000000006006
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The local candidates form the specified slice of their checked boundary group. -/
theorem slices603 : sheets603 = boundedSlice 512 480 6 sheetTable ∧
    shadows603 = boundedSlice 512 480 6 shadowTable := by decide +kernel
set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every local candidate inherits a physical boundary witness. -/
theorem boundaryAt603 (i : Nat) (hi : i < 6) : ∃ coefficient,
    reconX boundaryColumns coefficient = topJoin (lane 512 i sheets603) (lane 512 i shadows603) :=
  predicate_of_slice (fun a b => ∃ c, reconX boundaryColumns c = topJoin a b)
    512 count 480 6 sheetTable shadowTable _ _ (by decide) (by decide +kernel)
    boundaryAt slices603.1 slices603.2 i hi

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Affine reconstruction data for top fiber 603. -/
noncomputable def cert603 : AffineMaskCertificate := {
 beta := 0x7000000000000240200f80008008038000000006006
 sectionColumns := [(34,0x2),(35,0x4),(53,0x200000000000000000000000006000),(58,0x2000),(59,0x200000000000000000000000002000),(105,0x240200200008008008000000006006),(106,0x480000000010000000000000),(107,0x900000000020000000000000),(129,0x240200000008008000000000006006),(130,0x80000000000000000000000),(131,0x100000000000000000000000),(135,0x200000000000000000000000),(136,0x400000000000000000000000),(137,0x800000000000000000000000),(153,0x240000000008000000000000006000),(159,0x200000000000000000000000006),(160,0x3000000000000240000680008008018000000006000),(161,0x2000000000000000200480000000010000000000006),(177,0x240000000000000000000000006000)]
 kernelColumns := [(0,0x7000000000000240200f80008008038000000006006)]
 decoderColumns := [(170,0x1)]
 dimension := 1
 seeds := [(0x40000000000000000000,[0,1]),(0x80000000000000000000,[2,3]),(0x100000000000000000000,[4,5])] }

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every reconstructed candidate occurs in the local boundary table. -/
theorem checked603 : (cert603).checkIndexedBoundary 180 512 6 sheets603 shadows603 FiberData.topEColumns FiberData.topRColumns = true := by
  have hr : 0x12240000240000fc0000000000db6000db6000492 = reconX FiberData.topRColumns (cert603).beta := AffineSearchData.rhsChecked603.symm
  have h : (cert603).checkIndexedBoundaryCached 180 512 6 sheets603 shadows603 0x12240000240000fc0000000000db6000db6000492 DiagonalData.eColumn FiberData.topEColumns FiberData.topRColumns = true := by decide +kernel
  rwa [AffineMaskCertificate.checkIndexedBoundaryCached_eq _ _ _ _ _ _ _ _ _ _ topEColumn_eq hr] at h

end Quantum.Stabilizer.Homological.BB.Bravyi360.AffineBoundaryCached

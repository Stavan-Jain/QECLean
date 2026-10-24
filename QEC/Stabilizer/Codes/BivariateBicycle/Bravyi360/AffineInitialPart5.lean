/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_affine_search.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineInitialCommon
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineSearchPart5

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData
open PackedDigits BB.Bravyi360 BB.Bravyi360.FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 504. -/
noncomputable def lambdas504 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000004000008000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000008200000800000820000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 504. -/
noncomputable def rhs504 : Nat := 0x3f0000006c0000d800000240000240006c0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked504 : reconX topRColumns 0x1804000800004800800b40040018030004004018000 = rhs504 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 504. -/
theorem initialChecked504 : checkSearchInitial 8 180 12 rows504 lambdas504 0x400 0x1804000800004800800b40040018030004004018000 rhs504 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 504 has a listed outside support. -/
theorem complete504 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800004800800b40040018030004004018000)
    (hweight : bitCount 180 (outsideMask word 0x1804000800004800800b40040018030004004018000) ≤ 1) :
    outsideMask word 0x1804000800004800800b40040018030004004018000 ∈ allowed504 := by
  exact outside_mem_of_search 8 180 12 rows504 lambdas504 0x400 0x1804000800004800800b40040018030004004018000 rhs504 1
    topEColumns topETransposeColumns tree504 allowed504 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked504 checked504
    hw (he.trans rhsChecked504) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 505. -/
noncomputable def lambdas505 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000010400000000000e0400000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000c0000002000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000038000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 505. -/
noncomputable def rhs505 : Nat := 0x1b000036900000d8000002400002d000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked505 : reconX topRColumns 0x1805200a00000000240b00140010000004005000006 = rhs505 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 505. -/
theorem initialChecked505 : checkSearchInitial 8 180 12 rows505 lambdas505 0x11 0x1805200a00000000240b00140010000004005000006 rhs505 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 505 has a listed outside support. -/
theorem complete505 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1805200a00000000240b00140010000004005000006)
    (hweight : bitCount 180 (outsideMask word 0x1805200a00000000240b00140010000004005000006) ≤ 1) :
    outsideMask word 0x1805200a00000000240b00140010000004005000006 ∈ allowed505 := by
  exact outside_mem_of_search 8 180 12 rows505 lambdas505 0x11 0x1805200a00000000240b00140010000004005000006 rhs505 1
    topEColumns topETransposeColumns tree505 allowed505 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked505 checked505
    hw (he.trans rhsChecked505) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 506. -/
noncomputable def lambdas506 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000030000000000000000000000000000000880000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 506. -/
noncomputable def rhs506 : Nat := 0x6c0036b40000fe4000024000009000000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked506 : reconX topRColumns 0x1a00200000000000ee00d801800c004001000000000 = rhs506 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 506. -/
theorem initialChecked506 : checkSearchInitial 8 180 10 rows506 lambdas506 0x8 0x1a00200000000000ee00d801800c004001000000000 rhs506 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 506 has a listed outside support. -/
theorem complete506 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1a00200000000000ee00d801800c004001000000000)
    (hweight : bitCount 180 (outsideMask word 0x1a00200000000000ee00d801800c004001000000000) ≤ 1) :
    outsideMask word 0x1a00200000000000ee00d801800c004001000000000 ∈ allowed506 := by
  exact outside_mem_of_search 8 180 10 rows506 lambdas506 0x8 0x1a00200000000000ee00d801800c004001000000000 rhs506 1
    topEColumns topETransposeColumns tree506 allowed506 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked506 checked506
    hw (he.trans rhsChecked506) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 507. -/
noncomputable def lambdas507 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000a000008000008280000080000000000020000000000000000000000000000000000000000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 507. -/
noncomputable def rhs507 : Nat := 0x2dd8000090000090000002d000000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked507 : reconX topRColumns 0x1a00a00000000000fc08c00c0010020005000000000 = rhs507 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 507. -/
theorem initialChecked507 : checkSearchInitial 8 180 11 rows507 lambdas507 0x6 0x1a00a00000000000fc08c00c0010020005000000000 rhs507 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 507 has a listed outside support. -/
theorem complete507 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1a00a00000000000fc08c00c0010020005000000000)
    (hweight : bitCount 180 (outsideMask word 0x1a00a00000000000fc08c00c0010020005000000000) ≤ 1) :
    outsideMask word 0x1a00a00000000000fc08c00c0010020005000000000 ∈ allowed507 := by
  exact outside_mem_of_search 8 180 11 rows507 lambdas507 0x6 0x1a00a00000000000fc08c00c0010020005000000000 rhs507 1
    topEColumns topETransposeColumns tree507 allowed507 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked507 checked507
    hw (he.trans rhsChecked507) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 508. -/
noncomputable def lambdas508 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000c00000800000004000000000000000000000000000000000000000000040000080000082800000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000e00000000000000000000000000000002000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 508. -/
noncomputable def rhs508 : Nat := 0x24d80000d8000090000002d036d80000db600001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked508 : reconX topRColumns 0x1a00a00000001200940840080000020005000030005 = rhs508 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 508. -/
theorem initialChecked508 : checkSearchInitial 8 180 12 rows508 lambdas508 0x1 0x1a00a00000001200940840080000020005000030005 rhs508 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 508 has a listed outside support. -/
theorem complete508 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1a00a00000001200940840080000020005000030005)
    (hweight : bitCount 180 (outsideMask word 0x1a00a00000001200940840080000020005000030005) ≤ 1) :
    outsideMask word 0x1a00a00000001200940840080000020005000030005 ∈ allowed508 := by
  exact outside_mem_of_search 8 180 12 rows508 lambdas508 0x1 0x1a00a00000001200940840080000020005000030005 rhs508 1
    topEColumns topETransposeColumns tree508 allowed508 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked508 checked508
    hw (he.trans rhsChecked508) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 509. -/
noncomputable def lambdas509 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000e000000000000000000000000000000020000000000000000000000000000008000000000000000000000000000000600000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 509. -/
noncomputable def rhs509 : Nat := 0x2dd8003600000090000002d000009000db600001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked509 : reconX topRColumns 0x1a01800200000000b408400c0000010005001000005 = rhs509 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 509. -/
theorem initialChecked509 : checkSearchInitial 8 180 11 rows509 lambdas509 0x3 0x1a01800200000000b408400c0000010005001000005 rhs509 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 509 has a listed outside support. -/
theorem complete509 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1a01800200000000b408400c0000010005001000005)
    (hweight : bitCount 180 (outsideMask word 0x1a01800200000000b408400c0000010005001000005) ≤ 1) :
    outsideMask word 0x1a01800200000000b408400c0000010005001000005 ∈ allowed509 := by
  exact outside_mem_of_search 8 180 11 rows509 lambdas509 0x3 0x1a01800200000000b408400c0000010005001000005 rhs509 1
    topEColumns topETransposeColumns tree509 allowed509 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked509 checked509
    hw (he.trans rhsChecked509) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 510. -/
noncomputable def lambdas510 : Nat := (Nat.lor 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000020c00000400000e20000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004 (Nat.shiftLeft 0x800000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 510. -/
noncomputable def rhs510 : Nat := 0x2dd80024fc0000d8000002d000036000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked510 : reconX topRColumns 0x1a06600c000000000009000c0028010005006000000 = rhs510 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 510. -/
theorem initialChecked510 : checkSearchInitial 8 180 18 rows510 lambdas510 0x200 0x1a06600c000000000009000c0028010005006000000 rhs510 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 510 has a listed outside support. -/
theorem complete510 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1a06600c000000000009000c0028010005006000000)
    (hweight : bitCount 180 (outsideMask word 0x1a06600c000000000009000c0028010005006000000) ≤ 1) :
    outsideMask word 0x1a06600c000000000009000c0028010005006000000 ∈ allowed510 := by
  exact outside_mem_of_search 8 180 18 rows510 lambdas510 0x200 0x1a06600c000000000009000c0028010005006000000 rhs510 1
    topEColumns topETransposeColumns tree510 allowed510 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked510 checked510
    hw (he.trans rhsChecked510) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 511. -/
noncomputable def lambdas511 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 511. -/
noncomputable def rhs511 : Nat := 0x36d80000fdb000000000009900000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked511 : reconX topRColumns 0x1b00300000000000fc01c000000b000001800000000 = rhs511 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 511. -/
theorem initialChecked511 : checkSearchInitial 8 180 11 rows511 lambdas511 0x10 0x1b00300000000000fc01c000000b000001800000000 rhs511 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 511 has a listed outside support. -/
theorem complete511 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1b00300000000000fc01c000000b000001800000000)
    (hweight : bitCount 180 (outsideMask word 0x1b00300000000000fc01c000000b000001800000000) ≤ 1) :
    outsideMask word 0x1b00300000000000fc01c000000b000001800000000 ∈ allowed511 := by
  exact outside_mem_of_search 8 180 11 rows511 lambdas511 0x10 0x1b00300000000000fc01c000000b000001800000000 rhs511 1
    topEColumns topETransposeColumns tree511 allowed511 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked511 checked511
    hw (he.trans rhsChecked511) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 512. -/
noncomputable def lambdas512 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000030e00000000000000000000000000000201000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 512. -/
noncomputable def rhs512 : Nat := 0x36900000000000fc000003600000000092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked512 : reconX topRColumns 0x1c00c00000000000480f40000020038006000000005 = rhs512 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 512. -/
theorem initialChecked512 : checkSearchInitial 8 180 16 rows512 lambdas512 0x1 0x1c00c00000000000480f40000020038006000000005 rhs512 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 512 has a listed outside support. -/
theorem complete512 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1c00c00000000000480f40000020038006000000005)
    (hweight : bitCount 180 (outsideMask word 0x1c00c00000000000480f40000020038006000000005) ≤ 1) :
    outsideMask word 0x1c00c00000000000480f40000020038006000000005 ∈ allowed512 := by
  exact outside_mem_of_search 8 180 16 rows512 lambdas512 0x1 0x1c00c00000000000480f40000020038006000000005 rhs512 1
    topEColumns topETransposeColumns tree512 allowed512 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked512 checked512
    hw (he.trans rhsChecked512) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 513. -/
noncomputable def lambdas513 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000030c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 513. -/
noncomputable def rhs513 : Nat := 0x36900036900000fc0000036000009000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked513 : reconX topRColumns 0x1c01e00200000000000fc0000030008006001000000 = rhs513 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 513. -/
theorem initialChecked513 : checkSearchInitial 8 180 14 rows513 lambdas513 0x80 0x1c01e00200000000000fc0000030008006001000000 rhs513 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 513 has a listed outside support. -/
theorem complete513 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1c01e00200000000000fc0000030008006001000000)
    (hweight : bitCount 180 (outsideMask word 0x1c01e00200000000000fc0000030008006001000000) ≤ 1) :
    outsideMask word 0x1c01e00200000000000fc0000030008006001000000 ∈ allowed513 := by
  exact outside_mem_of_search 8 180 14 rows513 lambdas513 0x80 0x1c01e00200000000000fc0000030008006001000000 rhs513 1
    topEColumns topETransposeColumns tree513 allowed513 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked513 checked513
    hw (he.trans rhsChecked513) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 514. -/
noncomputable def lambdas514 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000180000000000000000000000000000001000000000000000000000000000000028000000800000820000000000000000080 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 514. -/
noncomputable def rhs514 : Nat := 0x3690000000000090000003600002400092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked514 : reconX topRColumns 0x1c04400800000000480f40000020020006004000005 = rhs514 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 514. -/
theorem initialChecked514 : checkSearchInitial 8 180 19 rows514 lambdas514 0x1 0x1c04400800000000480f40000020020006004000005 rhs514 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 514 has a listed outside support. -/
theorem complete514 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1c04400800000000480f40000020020006004000005)
    (hweight : bitCount 180 (outsideMask word 0x1c04400800000000480f40000020020006004000005) ≤ 1) :
    outsideMask word 0x1c04400800000000480f40000020020006004000005 ∈ allowed514 := by
  exact outside_mem_of_search 8 180 19 rows514 lambdas514 0x1 0x1c04400800000000480f40000020020006004000005 rhs514 1
    topEColumns topETransposeColumns tree514 allowed514 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked514 checked514
    hw (he.trans rhsChecked514) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 515. -/
noncomputable def lambdas515 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000030000000000000000000000000000000880000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 515. -/
noncomputable def rhs515 : Nat := 0xd800364b60002400000360000092400002404b6900036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked515 : reconX topRColumns 0x1c40000040000000e70070030008000001200200000 = rhs515 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 515. -/
theorem initialChecked515 : checkSearchInitial 8 180 12 rows515 lambdas515 0x8 0x1c40000040000000e70070030008000001200200000 rhs515 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 515 has a listed outside support. -/
theorem complete515 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1c40000040000000e70070030008000001200200000)
    (hweight : bitCount 180 (outsideMask word 0x1c40000040000000e70070030008000001200200000) ≤ 1) :
    outsideMask word 0x1c40000040000000e70070030008000001200200000 ∈ allowed515 := by
  exact outside_mem_of_search 8 180 12 rows515 lambdas515 0x8 0x1c40000040000000e70070030008000001200200000 rhs515 1
    topEColumns topETransposeColumns tree515 allowed515 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked515 checked515
    hw (he.trans rhsChecked515) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 516. -/
noncomputable def lambdas516 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000c00000031000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000828000008000000000000000010000010400000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 516. -/
noncomputable def rhs516 : Nat := 0x24000003f000000480000000d80d80012480000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked516 : reconX topRColumns 0x2000000000008206c00a803001c00100000001b0000 = rhs516 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 516. -/
theorem initialChecked516 : checkSearchInitial 8 180 12 rows516 lambdas516 0x8 0x2000000000008206c00a803001c00100000001b0000 rhs516 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 516 has a listed outside support. -/
theorem complete516 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2000000000008206c00a803001c00100000001b0000)
    (hweight : bitCount 180 (outsideMask word 0x2000000000008206c00a803001c00100000001b0000) ≤ 1) :
    outsideMask word 0x2000000000008206c00a803001c00100000001b0000 ∈ allowed516 := by
  exact outside_mem_of_search 8 180 12 rows516 lambdas516 0x8 0x2000000000008206c00a803001c00100000001b0000 rhs516 1
    topEColumns topETransposeColumns tree516 allowed516 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked516 checked516
    hw (he.trans rhsChecked516) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 517. -/
noncomputable def lambdas517 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 517. -/
noncomputable def rhs517 : Nat := 0x24900003f000000480000000db6000012480000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked517 : reconX topRColumns 0x2000000000009006e00a803401c0010000000180000 = rhs517 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 517. -/
theorem initialChecked517 : checkSearchInitial 8 180 10 rows517 lambdas517 0x8 0x2000000000009006e00a803401c0010000000180000 rhs517 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 517 has a listed outside support. -/
theorem complete517 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2000000000009006e00a803401c0010000000180000)
    (hweight : bitCount 180 (outsideMask word 0x2000000000009006e00a803401c0010000000180000) ≤ 1) :
    outsideMask word 0x2000000000009006e00a803401c0010000000180000 ∈ allowed517 := by
  exact outside_mem_of_search 8 180 10 rows517 lambdas517 0x8 0x2000000000009006e00a803401c0010000000180000 rhs517 1
    topEColumns topETransposeColumns tree517 allowed517 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked517 checked517
    hw (he.trans rhsChecked517) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 518. -/
noncomputable def lambdas518 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000200000008000002000000010000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 518. -/
noncomputable def rhs518 : Nat := 0x2402400025b480036fc001248000001b000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked518 : reconX topRColumns 0x208045805000800000000000002d0006028000c0040 = rhs518 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 518. -/
theorem initialChecked518 : checkSearchInitial 8 180 11 rows518 lambdas518 0x10 0x208045805000800000000000002d0006028000c0040 rhs518 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 518 has a listed outside support. -/
theorem complete518 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x208045805000800000000000002d0006028000c0040)
    (hweight : bitCount 180 (outsideMask word 0x208045805000800000000000002d0006028000c0040) ≤ 1) :
    outsideMask word 0x208045805000800000000000002d0006028000c0040 ∈ allowed518 := by
  exact outside_mem_of_search 8 180 11 rows518 lambdas518 0x10 0x208045805000800000000000002d0006028000c0040 rhs518 1
    topEColumns topETransposeColumns tree518 allowed518 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked518 checked518
    hw (he.trans rhsChecked518) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 519. -/
noncomputable def lambdas519 : Nat := 0x200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000028000000c4000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000018000010000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 519. -/
noncomputable def rhs519 : Nat := 0x240240006db000024d80012480000fc0000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked519 : reconX topRColumns 0x2080b4018800800000000000002d000002800e00040 = rhs519 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 519. -/
theorem initialChecked519 : checkSearchInitial 8 180 11 rows519 lambdas519 0x20 0x2080b4018800800000000000002d000002800e00040 rhs519 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 519 has a listed outside support. -/
theorem complete519 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2080b4018800800000000000002d000002800e00040)
    (hweight : bitCount 180 (outsideMask word 0x2080b4018800800000000000002d000002800e00040) ≤ 1) :
    outsideMask word 0x2080b4018800800000000000002d000002800e00040 ∈ allowed519 := by
  exact outside_mem_of_search 8 180 11 rows519 lambdas519 0x20 0x2080b4018800800000000000002d000002800e00040 rhs519 1
    topEColumns topETransposeColumns tree519 allowed519 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked519 checked519
    hw (he.trans rhsChecked519) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 520. -/
noncomputable def lambdas520 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000028000000000000000000000000000000080000000000000000000000000000002800000000000000000000000000000084000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000a00000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 520. -/
noncomputable def rhs520 : Nat := 0x264900000d80000000000012db6000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked520 : reconX topRColumns 0x2400400000009001fc01c0200010000002000180000 = rhs520 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 520. -/
theorem initialChecked520 : checkSearchInitial 8 180 11 rows520 lambdas520 0x4 0x2400400000009001fc01c0200010000002000180000 rhs520 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 520 has a listed outside support. -/
theorem complete520 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2400400000009001fc01c0200010000002000180000)
    (hweight : bitCount 180 (outsideMask word 0x2400400000009001fc01c0200010000002000180000) ≤ 1) :
    outsideMask word 0x2400400000009001fc01c0200010000002000180000 ∈ allowed520 := by
  exact outside_mem_of_search 8 180 11 rows520 lambdas520 0x4 0x2400400000009001fc01c0200010000002000180000 rhs520 1
    topEColumns topETransposeColumns tree520 allowed520 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked520 checked520
    hw (he.trans rhsChecked520) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 521. -/
noncomputable def lambdas521 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000c00000000000022000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 521. -/
noncomputable def rhs521 : Nat := 0x264900000252480000480012db600003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked521 : reconX topRColumns 0x24005f8038009001000000200028000002000040000 = rhs521 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 521. -/
theorem initialChecked521 : checkSearchInitial 8 180 10 rows521 lambdas521 0x91 0x24005f8038009001000000200028000002000040000 rhs521 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 521 has a listed outside support. -/
theorem complete521 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x24005f8038009001000000200028000002000040000)
    (hweight : bitCount 180 (outsideMask word 0x24005f8038009001000000200028000002000040000) ≤ 1) :
    outsideMask word 0x24005f8038009001000000200028000002000040000 ∈ allowed521 := by
  exact outside_mem_of_search 8 180 10 rows521 lambdas521 0x91 0x24005f8038009001000000200028000002000040000 rhs521 1
    topEColumns topETransposeColumns tree521 allowed521 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked521 checked521
    hw (he.trans rhsChecked521) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 522. -/
noncomputable def lambdas522 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 522. -/
noncomputable def rhs522 : Nat := 0x249000006d2000024d80012000000fc0000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked522 : reconX topRColumns 0x2400bc0188008000000000000028000002c00e00040 = rhs522 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 522. -/
theorem initialChecked522 : checkSearchInitial 8 180 9 rows522 lambdas522 0x8 0x2400bc0188008000000000000028000002c00e00040 rhs522 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 522 has a listed outside support. -/
theorem complete522 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2400bc0188008000000000000028000002c00e00040)
    (hweight : bitCount 180 (outsideMask word 0x2400bc0188008000000000000028000002c00e00040) ≤ 1) :
    outsideMask word 0x2400bc0188008000000000000028000002c00e00040 ∈ allowed522 := by
  exact outside_mem_of_search 8 180 9 rows522 lambdas522 0x8 0x2400bc0188008000000000000028000002c00e00040 rhs522 1
    topEColumns topETransposeColumns tree522 allowed522 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked522 checked522
    hw (he.trans rhsChecked522) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 523. -/
noncomputable def lambdas523 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000030000000c400000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 523. -/
noncomputable def rhs523 : Nat := 0xfc00006c0000000036d80000492000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked523 : reconX topRColumns 0x3000000000001200dc0700080038018000000030000 = rhs523 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 523. -/
theorem initialChecked523 : checkSearchInitial 8 180 10 rows523 lambdas523 0x2 0x3000000000001200dc0700080038018000000030000 rhs523 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 523 has a listed outside support. -/
theorem complete523 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3000000000001200dc0700080038018000000030000)
    (hweight : bitCount 180 (outsideMask word 0x3000000000001200dc0700080038018000000030000) ≤ 1) :
    outsideMask word 0x3000000000001200dc0700080038018000000030000 ∈ allowed523 := by
  exact outside_mem_of_search 8 180 10 rows523 lambdas523 0x2 0x3000000000001200dc0700080038018000000030000 rhs523 1
    topEColumns topETransposeColumns tree523 allowed523 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked523 checked523
    hw (he.trans rhsChecked523) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 524. -/
noncomputable def lambdas524 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000030000010000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000004000004000000000000000000000000200000040000000000000000000000000000038000010400000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 524. -/
noncomputable def rhs524 : Nat := 0x1b4800120000006c0000000024024024b490006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked524 : reconX topRColumns 0x30000000000020820802c005008001800000002d028 = rhs524 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 524. -/
theorem initialChecked524 : checkSearchInitial 8 180 11 rows524 lambdas524 0x41 0x30000000000020820802c005008001800000002d028 rhs524 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 524 has a listed outside support. -/
theorem complete524 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30000000000020820802c005008001800000002d028)
    (hweight : bitCount 180 (outsideMask word 0x30000000000020820802c005008001800000002d028) ≤ 1) :
    outsideMask word 0x30000000000020820802c005008001800000002d028 ∈ allowed524 := by
  exact outside_mem_of_search 8 180 11 rows524 lambdas524 0x41 0x30000000000020820802c005008001800000002d028 rhs524 1
    topEColumns topETransposeColumns tree524 allowed524 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked524 checked524
    hw (he.trans rhsChecked524) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 525. -/
noncomputable def lambdas525 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000300000004000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000010400000200000200000000000000000020000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 525. -/
noncomputable def rhs525 : Nat := 0x1b0000094800006c00000000249000366e400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked525 : reconX topRColumns 0x3000000000002401280440040050018000000028035 = rhs525 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 525. -/
theorem initialChecked525 : checkSearchInitial 8 180 12 rows525 lambdas525 0x81 0x3000000000002401280440040050018000000028035 rhs525 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 525 has a listed outside support. -/
theorem complete525 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3000000000002401280440040050018000000028035)
    (hweight : bitCount 180 (outsideMask word 0x3000000000002401280440040050018000000028035) ≤ 1) :
    outsideMask word 0x3000000000002401280440040050018000000028035 ∈ allowed525 := by
  exact outside_mem_of_search 8 180 12 rows525 lambdas525 0x81 0x3000000000002401280440040050018000000028035 rhs525 1
    topEColumns topETransposeColumns tree525 allowed525 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked525 checked525
    hw (he.trans rhsChecked525) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 526. -/
noncomputable def lambdas526 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000030000010000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000410000008000000200000000000000020000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 526. -/
noncomputable def rhs526 : Nat := 0x1b0000122400006c00000000249000246f60006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked526 : reconX topRColumns 0x300000000000240224028004008801800000002802e = rhs526 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 526. -/
theorem initialChecked526 : checkSearchInitial 8 180 12 rows526 lambdas526 0x41 0x300000000000240224028004008801800000002802e rhs526 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 526 has a listed outside support. -/
theorem complete526 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300000000000240224028004008801800000002802e)
    (hweight : bitCount 180 (outsideMask word 0x300000000000240224028004008801800000002802e) ≤ 1) :
    outsideMask word 0x300000000000240224028004008801800000002802e ∈ allowed526 := by
  exact outside_mem_of_search 8 180 12 rows526 lambdas526 0x41 0x300000000000240224028004008801800000002802e rhs526 1
    topEColumns topETransposeColumns tree526 allowed526 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked526 checked526
    hw (he.trans rhsChecked526) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 527. -/
noncomputable def lambdas527 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000010000010600000200000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 527. -/
noncomputable def rhs527 : Nat := 0x1b0000360000006c0000000024900024b40000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked527 : reconX topRColumns 0x3000000000002406800ac0040180018000000028030 = rhs527 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 527. -/
theorem initialChecked527 : checkSearchInitial 8 180 15 rows527 lambdas527 0x1 0x3000000000002406800ac0040180018000000028030 rhs527 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 527 has a listed outside support. -/
theorem complete527 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3000000000002406800ac0040180018000000028030)
    (hweight : bitCount 180 (outsideMask word 0x3000000000002406800ac0040180018000000028030) ≤ 1) :
    outsideMask word 0x3000000000002406800ac0040180018000000028030 ∈ allowed527 := by
  exact outside_mem_of_search 8 180 15 rows527 lambdas527 0x1 0x3000000000002406800ac0040180018000000028030 rhs527 1
    topEColumns topETransposeColumns tree527 allowed527 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked527 checked527
    hw (he.trans rhsChecked527) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 528. -/
noncomputable def lambdas528 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000003800000000000000000000000000000010000000000000000000000000004000004000000000000000000000000200000040000000000000000000000000000020000000600000600000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 528. -/
noncomputable def rhs528 : Nat := 0x124800000000006c0000000012da4000249000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked528 : reconX topRColumns 0x30000000000032806806c001000001800000001d000 = rhs528 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 528. -/
theorem initialChecked528 : checkSearchInitial 8 180 10 rows528 lambdas528 0x4 0x30000000000032806806c001000001800000001d000 rhs528 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 528 has a listed outside support. -/
theorem complete528 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30000000000032806806c001000001800000001d000)
    (hweight : bitCount 180 (outsideMask word 0x30000000000032806806c001000001800000001d000) ≤ 1) :
    outsideMask word 0x30000000000032806806c001000001800000001d000 ∈ allowed528 := by
  exact outside_mem_of_search 8 180 10 rows528 lambdas528 0x4 0x30000000000032806806c001000001800000001d000 rhs528 1
    topEColumns topETransposeColumns tree528 allowed528 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked528 checked528
    hw (he.trans rhsChecked528) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 529. -/
noncomputable def lambdas529 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000003800000000000000000000000000000010000000000000000000000000002000002000000000000000000000000200000040000000000000000000000000000020000000600000600000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 529. -/
noncomputable def rhs529 : Nat := 0x122400000000006c0000000012936000240000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked529 : reconX topRColumns 0x30000000000034406406c000800001800000001e000 = rhs529 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 529. -/
theorem initialChecked529 : checkSearchInitial 8 180 10 rows529 lambdas529 0x4 0x30000000000034406406c000800001800000001e000 rhs529 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 529 has a listed outside support. -/
theorem complete529 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30000000000034406406c000800001800000001e000)
    (hweight : bitCount 180 (outsideMask word 0x30000000000034406406c000800001800000001e000) ≤ 1) :
    outsideMask word 0x30000000000034406406c000800001800000001e000 ∈ allowed529 := by
  exact outside_mem_of_search 8 180 10 rows529 lambdas529 0x4 0x30000000000034406406c000800001800000001e000 rhs529 1
    topEColumns topETransposeColumns tree529 allowed529 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked529 checked529
    hw (he.trans rhsChecked529) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 530. -/
noncomputable def lambdas530 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000003000000040000008000000000000000000000000000000000000000000000000280000080000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000030000000400000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 530. -/
noncomputable def rhs530 : Nat := 0x120000094800006c00000000124800366e400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked530 : reconX topRColumns 0x3000000000003601080440000050018000000018035 = rhs530 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 530. -/
theorem initialChecked530 : checkSearchInitial 8 180 11 rows530 lambdas530 0x101 0x3000000000003601080440000050018000000018035 rhs530 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 530 has a listed outside support. -/
theorem complete530 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3000000000003601080440000050018000000018035)
    (hweight : bitCount 180 (outsideMask word 0x3000000000003601080440000050018000000018035) ≤ 1) :
    outsideMask word 0x3000000000003601080440000050018000000018035 ∈ allowed530 := by
  exact outside_mem_of_search 8 180 11 rows530 lambdas530 0x101 0x3000000000003601080440000050018000000018035 rhs530 1
    topEColumns topETransposeColumns tree530 allowed530 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked530 checked530
    hw (he.trans rhsChecked530) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 531. -/
noncomputable def lambdas531 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000030000010000000080000000000000000000000000000000000000000000000002800000020000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000280000002000000400000000000000000000000000000000000000000000000000c00000400000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 531. -/
noncomputable def rhs531 : Nat := 0x120000122400006c00000000124800246f60006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked531 : reconX topRColumns 0x300000000000360204028000008801800000001802e = rhs531 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 531. -/
theorem initialChecked531 : checkSearchInitial 8 180 13 rows531 lambdas531 0x201 0x300000000000360204028000008801800000001802e rhs531 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 531 has a listed outside support. -/
theorem complete531 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300000000000360204028000008801800000001802e)
    (hweight : bitCount 180 (outsideMask word 0x300000000000360204028000008801800000001802e) ≤ 1) :
    outsideMask word 0x300000000000360204028000008801800000001802e ∈ allowed531 := by
  exact outside_mem_of_search 8 180 13 rows531 lambdas531 0x201 0x300000000000360204028000008801800000001802e rhs531 1
    topEColumns topETransposeColumns tree531 allowed531 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked531 checked531
    hw (he.trans rhsChecked531) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 532. -/
noncomputable def lambdas532 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000003000000040000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000400000000000000000000000800000020000002000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 532. -/
noncomputable def rhs532 : Nat := 0x49b0000004800006c0000000900900009b6400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked532 : reconX topRColumns 0x3000000000010402080640440010018000000168005 = rhs532 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 532. -/
theorem initialChecked532 : checkSearchInitial 8 180 12 rows532 lambdas532 0x100 0x3000000000010402080640440010018000000168005 rhs532 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 532 has a listed outside support. -/
theorem complete532 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3000000000010402080640440010018000000168005)
    (hweight : bitCount 180 (outsideMask word 0x3000000000010402080640440010018000000168005) ≤ 1) :
    outsideMask word 0x3000000000010402080640440010018000000168005 ∈ allowed532 := by
  exact outside_mem_of_search 8 180 12 rows532 lambdas532 0x100 0x3000000000010402080640440010018000000168005 rhs532 1
    topEColumns topETransposeColumns tree532 allowed532 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked532 checked532
    hw (he.trans rhsChecked532) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 533. -/
noncomputable def lambdas533 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000a000000210000000000000000000000000000000038000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000200000180000006000000000000000000000001000000000000000000000000020000000600000600000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 533. -/
noncomputable def rhs533 : Nat := 0x4920000000000006c0000000936480009240000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked533 : reconX topRColumns 0x30000000000116026006c0400000018000000158000 = rhs533 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 533. -/
theorem initialChecked533 : checkSearchInitial 8 180 11 rows533 lambdas533 0x8 0x30000000000116026006c0400000018000000158000 rhs533 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 533 has a listed outside support. -/
theorem complete533 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30000000000116026006c0400000018000000158000)
    (hweight : bitCount 180 (outsideMask word 0x30000000000116026006c0400000018000000158000) ≤ 1) :
    outsideMask word 0x30000000000116026006c0400000018000000158000 ∈ allowed533 := by
  exact outside_mem_of_search 8 180 11 rows533 lambdas533 0x8 0x30000000000116026006c0400000018000000158000 rhs533 1
    topEColumns topETransposeColumns tree533 allowed533 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked533 checked533
    hw (he.trans rhsChecked533) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 534. -/
noncomputable def lambdas534 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000030000000c000008800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000020800000000000201000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 534. -/
noncomputable def rhs534 : Nat := 0x1b0000369000006c0000000024909000b6400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked534 : reconX topRColumns 0x3001200200002400080640040010028000001028005 = rhs534 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 534. -/
theorem initialChecked534 : checkSearchInitial 8 180 13 rows534 lambdas534 0x400 0x3001200200002400080640040010028000001028005 rhs534 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 534 has a listed outside support. -/
theorem complete534 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3001200200002400080640040010028000001028005)
    (hweight : bitCount 180 (outsideMask word 0x3001200200002400080640040010028000001028005) ≤ 1) :
    outsideMask word 0x3001200200002400080640040010028000001028005 ∈ allowed534 := by
  exact outside_mem_of_search 8 180 13 rows534 lambdas534 0x400 0x3001200200002400080640040010028000001028005 rhs534 1
    topEColumns topETransposeColumns tree534 allowed534 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked534 checked534
    hw (he.trans rhsChecked534) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 535. -/
noncomputable def lambdas535 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000003800000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000020000000e00000e00000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 535. -/
noncomputable def rhs535 : Nat := 0x12000036d800006c0000000012489000240000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked535 : reconX topRColumns 0x30012002000036006006c0000000028000001018000 = rhs535 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 535. -/
theorem initialChecked535 : checkSearchInitial 8 180 11 rows535 lambdas535 0x4 0x30012002000036006006c0000000028000001018000 rhs535 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 535 has a listed outside support. -/
theorem complete535 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30012002000036006006c0000000028000001018000)
    (hweight : bitCount 180 (outsideMask word 0x30012002000036006006c0000000028000001018000) ≤ 1) :
    outsideMask word 0x30012002000036006006c0000000028000001018000 ∈ allowed535 := by
  exact outside_mem_of_search 8 180 11 rows535 lambdas535 0x4 0x30012002000036006006c0000000028000001018000 rhs535 1
    topEColumns topETransposeColumns tree535 allowed535 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked535 checked535
    hw (he.trans rhsChecked535) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 536. -/
noncomputable def lambdas536 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000300000004000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000038000010400000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 536. -/
noncomputable def rhs536 : Nat := 0x1b000024d80000480000000024912000b6400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked536 : reconX topRColumns 0x3002400400002400080640040010030000002028005 = rhs536 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 536. -/
theorem initialChecked536 : checkSearchInitial 8 180 12 rows536 lambdas536 0x81 0x3002400400002400080640040010030000002028005 rhs536 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 536 has a listed outside support. -/
theorem complete536 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3002400400002400080640040010030000002028005)
    (hweight : bitCount 180 (outsideMask word 0x3002400400002400080640040010030000002028005) ≤ 1) :
    outsideMask word 0x3002400400002400080640040010030000002028005 ∈ allowed536 := by
  exact outside_mem_of_search 8 180 12 rows536 lambdas536 0x81 0x3002400400002400080640040010030000002028005 rhs536 1
    topEColumns topETransposeColumns tree536 allowed536 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked536 checked536
    hw (he.trans rhsChecked536) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 537. -/
noncomputable def lambdas537 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000003800000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000020000000e00000e00000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 537. -/
noncomputable def rhs537 : Nat := 0x12000024900000480000000012492000240000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked537 : reconX topRColumns 0x30024004000036006006c0000000030000002018000 = rhs537 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 537. -/
theorem initialChecked537 : checkSearchInitial 8 180 11 rows537 lambdas537 0x4 0x30024004000036006006c0000000030000002018000 rhs537 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 537 has a listed outside support. -/
theorem complete537 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30024004000036006006c0000000030000002018000)
    (hweight : bitCount 180 (outsideMask word 0x30024004000036006006c0000000030000002018000) ≤ 1) :
    outsideMask word 0x30024004000036006006c0000000030000002018000 ∈ allowed537 := by
  exact outside_mem_of_search 8 180 11 rows537 lambdas537 0x4 0x30024004000036006006c0000000030000002018000 rhs537 1
    topEColumns topETransposeColumns tree537 allowed537 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked537 checked537
    hw (he.trans rhsChecked537) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 538. -/
noncomputable def lambdas538 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000038000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 538. -/
noncomputable def rhs538 : Nat := 0x9000012da400048900000000001b480000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked538 : reconX topRColumns 0x30032806800000000006c00c0000005000003400000 = rhs538 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 538. -/
theorem initialChecked538 : checkSearchInitial 8 180 10 rows538 lambdas538 0x9 0x30032806800000000006c00c0000005000003400000 rhs538 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 538 has a listed outside support. -/
theorem complete538 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30032806800000000006c00c0000005000003400000)
    (hweight : bitCount 180 (outsideMask word 0x30032806800000000006c00c0000005000003400000) ≤ 1) :
    outsideMask word 0x30032806800000000006c00c0000005000003400000 ∈ allowed538 := by
  exact outside_mem_of_search 8 180 10 rows538 lambdas538 0x9 0x30032806800000000006c00c0000005000003400000 rhs538 1
    topEColumns topETransposeColumns tree538 allowed538 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked538 checked538
    hw (he.trans rhsChecked538) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 539. -/
noncomputable def lambdas539 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000038000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 539. -/
noncomputable def rhs539 : Nat := 0x900001293600048000000000001b240000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked539 : reconX topRColumns 0x30034406400000000006c00c0000006000003200000 = rhs539 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 539. -/
theorem initialChecked539 : checkSearchInitial 8 180 10 rows539 lambdas539 0x9 0x30034406400000000006c00c0000006000003200000 rhs539 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 539 has a listed outside support. -/
theorem complete539 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30034406400000000006c00c0000006000003200000)
    (hweight : bitCount 180 (outsideMask word 0x30034406400000000006c00c0000006000003200000) ≤ 1) :
    outsideMask word 0x30034406400000000006c00c0000006000003200000 ∈ allowed539 := by
  exact outside_mem_of_search 8 180 10 rows539 lambdas539 0x9 0x30034406400000000006c00c0000006000003200000 rhs539 1
    topEColumns topETransposeColumns tree539 allowed539 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked539 checked539
    hw (he.trans rhsChecked539) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 540. -/
noncomputable def lambdas540 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000038000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 540. -/
noncomputable def rhs540 : Nat := 0x90000126c000048000000000001b000db6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked540 : reconX topRColumns 0x30036006000000002406800c0008000000003000006 = rhs540 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 540. -/
theorem initialChecked540 : checkSearchInitial 8 180 10 rows540 lambdas540 0x9 0x30036006000000002406800c0008000000003000006 rhs540 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 540 has a listed outside support. -/
theorem complete540 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30036006000000002406800c0008000000003000006)
    (hweight : bitCount 180 (outsideMask word 0x30036006000000002406800c0008000000003000006) ≤ 1) :
    outsideMask word 0x30036006000000002406800c0008000000003000006 ∈ allowed540 := by
  exact outside_mem_of_search 8 180 10 rows540 lambdas540 0x9 0x30036006000000002406800c0008000000003000006 rhs540 1
    topEColumns topETransposeColumns tree540 allowed540 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked540 checked540
    hw (he.trans rhsChecked540) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 541. -/
noncomputable def lambdas541 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000038000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 541. -/
noncomputable def rhs541 : Nat := 0x900001200000048000000000001b00092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked541 : reconX topRColumns 0x30036006000000004806400c0010000000003000005 = rhs541 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 541. -/
theorem initialChecked541 : checkSearchInitial 8 180 10 rows541 lambdas541 0x9 0x30036006000000004806400c0010000000003000005 rhs541 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 541 has a listed outside support. -/
theorem complete541 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30036006000000004806400c0010000000003000005)
    (hweight : bitCount 180 (outsideMask word 0x30036006000000004806400c0010000000003000005) ≤ 1) :
    outsideMask word 0x30036006000000004806400c0010000000003000005 ∈ allowed541 := by
  exact outside_mem_of_search 8 180 10 rows541 lambdas541 0x9 0x30036006000000004806400c0010000000003000005 rhs541 1
    topEColumns topETransposeColumns tree541 allowed541 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked541 checked541
    hw (he.trans rhsChecked541) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 542. -/
noncomputable def lambdas542 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 542. -/
noncomputable def rhs542 : Nat := 0x900001b48000048000000000001b036d80000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked542 : reconX topRColumns 0x30036006000000012004c00c0040000000003000030 = rhs542 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 542. -/
theorem initialChecked542 : checkSearchInitial 8 180 10 rows542 lambdas542 0x41 0x30036006000000012004c00c0040000000003000030 rhs542 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 542 has a listed outside support. -/
theorem complete542 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30036006000000012004c00c0040000000003000030)
    (hweight : bitCount 180 (outsideMask word 0x30036006000000012004c00c0040000000003000030) ≤ 1) :
    outsideMask word 0x30036006000000012004c00c0040000000003000030 ∈ allowed542 := by
  exact outside_mem_of_search 8 180 10 rows542 lambdas542 0x41 0x30036006000000012004c00c0040000000003000030 rhs542 1
    topEColumns topETransposeColumns tree542 allowed542 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked542 checked542
    hw (he.trans rhsChecked542) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 543. -/
noncomputable def lambdas543 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 543. -/
noncomputable def rhs543 : Nat := 0x900000048000048000000000001b0249000006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked543 : reconX topRColumns 0x30036006000000024002c00c0080000000003000028 = rhs543 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 543. -/
theorem initialChecked543 : checkSearchInitial 8 180 10 rows543 lambdas543 0x41 0x30036006000000024002c00c0080000000003000028 rhs543 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 543 has a listed outside support. -/
theorem complete543 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30036006000000024002c00c0080000000003000028)
    (hweight : bitCount 180 (outsideMask word 0x30036006000000024002c00c0080000000003000028) ≤ 1) :
    outsideMask word 0x30036006000000024002c00c0080000000003000028 ∈ allowed543 := by
  exact outside_mem_of_search 8 180 10 rows543 lambdas543 0x41 0x30036006000000024002c00c0080000000003000028 rhs543 1
    topEColumns topETransposeColumns tree543 allowed543 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked543 checked543
    hw (he.trans rhsChecked543) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 544. -/
noncomputable def lambdas544 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 544. -/
noncomputable def rhs544 : Nat := 0x12480000480000000036d9b000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked544 : reconX topRColumns 0x30036006000012002006c0080000000000003030000 = rhs544 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 544. -/
theorem initialChecked544 : checkSearchInitial 8 180 10 rows544 lambdas544 0x41 0x30036006000012002006c0080000000000003030000 rhs544 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 544 has a listed outside support. -/
theorem complete544 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30036006000012002006c0080000000000003030000)
    (hweight : bitCount 180 (outsideMask word 0x30036006000012002006c0080000000000003030000) ≤ 1) :
    outsideMask word 0x30036006000012002006c0080000000000003030000 ∈ allowed544 := by
  exact outside_mem_of_search 8 180 10 rows544 lambdas544 0x41 0x30036006000012002006c0080000000000003030000 rhs544 1
    topEColumns topETransposeColumns tree544 allowed544 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked544 checked544
    hw (he.trans rhsChecked544) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 545. -/
noncomputable def lambdas545 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 545. -/
noncomputable def rhs545 : Nat := 0x1b00001248000048000000002491b000240000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked545 : reconX topRColumns 0x30036006000024004006c0040000000000003028000 = rhs545 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 545. -/
theorem initialChecked545 : checkSearchInitial 8 180 10 rows545 lambdas545 0x41 0x30036006000024004006c0040000000000003028000 rhs545 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 545 has a listed outside support. -/
theorem complete545 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30036006000024004006c0040000000000003028000)
    (hweight : bitCount 180 (outsideMask word 0x30036006000024004006c0040000000000003028000) ≤ 1) :
    outsideMask word 0x30036006000024004006c0040000000000003028000 ∈ allowed545 := by
  exact outside_mem_of_search 8 180 10 rows545 lambdas545 0x41 0x30036006000024004006c0040000000000003028000 rhs545 1
    topEColumns topETransposeColumns tree545 allowed545 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked545 checked545
    hw (he.trans rhsChecked545) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 546. -/
noncomputable def lambdas546 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000020000000c00000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 546. -/
noncomputable def rhs546 : Nat := 0x1b00001b0000000000000000249240126c00006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked546 : reconX topRColumns 0x30048008000024032000c00400c0000000004028018 = rhs546 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 546. -/
theorem initialChecked546 : checkSearchInitial 8 180 13 rows546 lambdas546 0x1 0x30048008000024032000c00400c0000000004028018 rhs546 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 546 has a listed outside support. -/
theorem complete546 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30048008000024032000c00400c0000000004028018)
    (hweight : bitCount 180 (outsideMask word 0x30048008000024032000c00400c0000000004028018) ≤ 1) :
    outsideMask word 0x30048008000024032000c00400c0000000004028018 ∈ allowed546 := by
  exact outside_mem_of_search 8 180 13 rows546 lambdas546 0x1 0x30048008000024032000c00400c0000000004028018 rhs546 1
    topEColumns topETransposeColumns tree546 allowed546 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked546 checked546
    hw (he.trans rhsChecked546) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 547. -/
noncomputable def lambdas547 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000002000000000000044000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000038400000000000000000000000000000804000000000000000000000000000000000001800000000000000000000000000000010000000000000000000000000380000006000000000000000000000008000000040000000000000000000000038000000600000000000000000c000004000000020000000000000000000000000000000000000000000000038400000200000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 547. -/
noncomputable def rhs547 : Nat := 0x120000004800000000000000124a4000b6400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked547 : reconX topRColumns 0x3004800800003600280640000010000000004018005 = rhs547 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 547. -/
theorem initialChecked547 : checkSearchInitial 8 180 15 rows547 lambdas547 0x14 0x3004800800003600280640000010000000004018005 rhs547 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 547 has a listed outside support. -/
theorem complete547 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3004800800003600280640000010000000004018005)
    (hweight : bitCount 180 (outsideMask word 0x3004800800003600280640000010000000004018005) ≤ 1) :
    outsideMask word 0x3004800800003600280640000010000000004018005 ∈ allowed547 := by
  exact outside_mem_of_search 8 180 15 rows547 lambdas547 0x14 0x3004800800003600280640000010000000004018005 rhs547 1
    topEColumns topETransposeColumns tree547 allowed547 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked547 checked547
    hw (he.trans rhsChecked547) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 548. -/
noncomputable def lambdas548 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000038c4000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000003820000000000000000000000000000080400000000000000000000000000000380000006000000000000000000000008000000040000000000000000000000000000000000000000000000000c00000400000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 548. -/
noncomputable def rhs548 : Nat := 0x120000002400000000000000124a4000ff6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked548 : reconX topRColumns 0x3004800800003600440680000008000000004018006 = rhs548 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 548. -/
theorem initialChecked548 : checkSearchInitial 8 180 12 rows548 lambdas548 0x7 0x3004800800003600440680000008000000004018006 rhs548 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 548 has a listed outside support. -/
theorem complete548 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3004800800003600440680000008000000004018006)
    (hweight : bitCount 180 (outsideMask word 0x3004800800003600440680000008000000004018006) ≤ 1) :
    outsideMask word 0x3004800800003600440680000008000000004018006 ∈ allowed548 := by
  exact outside_mem_of_search 8 180 12 rows548 lambdas548 0x7 0x3004800800003600440680000008000000004018006 rhs548 1
    topEColumns topETransposeColumns tree548 allowed548 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked548 checked548
    hw (he.trans rhsChecked548) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 549. -/
noncomputable def lambdas549 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000002000000000000044000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000238000000000000000000000000000020100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000030000000400000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 549. -/
noncomputable def rhs549 : Nat := 0x120000090000000000000000124a4036fc0000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked549 : reconX topRColumns 0x30048008000036014004c0000040000000004018030 = rhs549 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 549. -/
theorem initialChecked549 : checkSearchInitial 8 180 11 rows549 lambdas549 0x9 0x30048008000036014004c0000040000000004018030 rhs549 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 549 has a listed outside support. -/
theorem complete549 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30048008000036014004c0000040000000004018030)
    (hweight : bitCount 180 (outsideMask word 0x30048008000036014004c0000040000000004018030) ≤ 1) :
    outsideMask word 0x30048008000036014004c0000040000000004018030 ∈ allowed549 := by
  exact outside_mem_of_search 8 180 11 rows549 lambdas549 0x9 0x30048008000036014004c0000040000000004018030 rhs549 1
    topEColumns topETransposeColumns tree549 allowed549 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked549 checked549
    hw (he.trans rhsChecked549) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 550. -/
noncomputable def lambdas550 : Nat := (Nat.lor 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000030000010000000400000800000004000000000000000000000000000000000043800000000000000000000000000002010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000380000180000000000000000300000004000000800000000000000000000000000000000600000000000000000000000000000004 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 550. -/
noncomputable def rhs550 : Nat := 0x120000120000000000000000124a4024b400006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked550 : reconX topRColumns 0x30048008000036022002c0000080000000004018028 = rhs550 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 550. -/
theorem initialChecked550 : checkSearchInitial 8 180 18 rows550 lambdas550 0x60 0x30048008000036022002c0000080000000004018028 rhs550 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 550 has a listed outside support. -/
theorem complete550 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30048008000036022002c0000080000000004018028)
    (hweight : bitCount 180 (outsideMask word 0x30048008000036022002c0000080000000004018028) ≤ 1) :
    outsideMask word 0x30048008000036022002c0000080000000004018028 ∈ allowed550 := by
  exact outside_mem_of_search 8 180 18 rows550 lambdas550 0x60 0x30048008000036022002c0000080000000004018028 rhs550 1
    topEColumns topETransposeColumns tree550 allowed550 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked550 checked550
    hw (he.trans rhsChecked550) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 551. -/
noncomputable def lambdas551 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000018000000000000600000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 551. -/
noncomputable def rhs551 : Nat := 0x360000000000000000000000124a4000480000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked551 : reconX topRColumns 0x3004800800007e00e006c0100000000000004000000 = rhs551 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 551. -/
theorem initialChecked551 : checkSearchInitial 8 180 11 rows551 lambdas551 0x18 0x3004800800007e00e006c0100000000000004000000 rhs551 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 551 has a listed outside support. -/
theorem complete551 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3004800800007e00e006c0100000000000004000000)
    (hweight : bitCount 180 (outsideMask word 0x3004800800007e00e006c0100000000000004000000) ≤ 1) :
    outsideMask word 0x3004800800007e00e006c0100000000000004000000 ∈ allowed551 := by
  exact outside_mem_of_search 8 180 11 rows551 lambdas551 0x18 0x3004800800007e00e006c0100000000000004000000 rhs551 1
    topEColumns topETransposeColumns tree551 allowed551 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked551 checked551
    hw (he.trans rhsChecked551) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 552. -/
noncomputable def lambdas552 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000080000080400000000000000000000000000000400000018000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 552. -/
noncomputable def rhs552 : Nat := 0x49b00001200000000000000090092402db400006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked552 : reconX topRColumns 0x30048008000104000002c0440080000000004168028 = rhs552 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 552. -/
theorem initialChecked552 : checkSearchInitial 8 180 9 rows552 lambdas552 0x1 0x30048008000104000002c0440080000000004168028 rhs552 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 552 has a listed outside support. -/
theorem complete552 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30048008000104000002c0440080000000004168028)
    (hweight : bitCount 180 (outsideMask word 0x30048008000104000002c0440080000000004168028) ≤ 1) :
    outsideMask word 0x30048008000104000002c0440080000000004168028 ∈ allowed552 := by
  exact outside_mem_of_search 8 180 9 rows552 lambdas552 0x1 0x30048008000104000002c0440080000000004168028 rhs552 1
    topEColumns topETransposeColumns tree552 allowed552 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked552 checked552
    hw (he.trans rhsChecked552) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 553. -/
noncomputable def lambdas553 : Nat := (Nat.lor 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000002380000300000200000008000000000000000000400000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 553. -/
noncomputable def rhs553 : Nat := 0x6d200002dd80024fc0000900000009000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked553 : reconX topRColumns 0x30052002000000000047c06000c0108020001000000 = rhs553 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 553. -/
theorem initialChecked553 : checkSearchInitial 8 180 19 rows553 lambdas553 0x2 0x30052002000000000047c06000c0108020001000000 rhs553 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 553 has a listed outside support. -/
theorem complete553 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30052002000000000047c06000c0108020001000000)
    (hweight : bitCount 180 (outsideMask word 0x30052002000000000047c06000c0108020001000000) ≤ 1) :
    outsideMask word 0x30052002000000000047c06000c0108020001000000 ∈ allowed553 := by
  exact outside_mem_of_search 8 180 19 rows553 lambdas553 0x2 0x30052002000000000047c06000c0108020001000000 rhs553 1
    topEColumns topETransposeColumns tree553 allowed553 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked553 checked553
    hw (he.trans rhsChecked553) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 554. -/
noncomputable def lambdas554 : Nat := (Nat.lor 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000004380000280000200000008000000000000000000800000000000000000000000000000000a00000000000000000000000000000002 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 554. -/
noncomputable def rhs554 : Nat := 0x6d200003f900024d80000900000012000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked554 : reconX topRColumns 0x30064004000000000047c06000c0110020002000000 = rhs554 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 554. -/
theorem initialChecked554 : checkSearchInitial 8 180 19 rows554 lambdas554 0x2 0x30064004000000000047c06000c0110020002000000 rhs554 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 554 has a listed outside support. -/
theorem complete554 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30064004000000000047c06000c0110020002000000)
    (hweight : bitCount 180 (outsideMask word 0x30064004000000000047c06000c0110020002000000) ≤ 1) :
    outsideMask word 0x30064004000000000047c06000c0110020002000000 ∈ allowed554 := by
  exact outside_mem_of_search 8 180 19 rows554 lambdas554 0x2 0x30064004000000000047c06000c0110020002000000 rhs554 1
    topEColumns topETransposeColumns tree554 allowed554 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked554 checked554
    hw (he.trans rhsChecked554) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 555. -/
noncomputable def lambdas555 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 555. -/
noncomputable def rhs555 : Nat := 0x9000da448000048000000000025b000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked555 : reconX topRColumns 0x300a6016000000000006c00c000018000000b000000 = rhs555 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 555. -/
theorem initialChecked555 : checkSearchInitial 8 180 10 rows555 lambdas555 0x41 0x300a6016000000000006c00c000018000000b000000 rhs555 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 555 has a listed outside support. -/
theorem complete555 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300a6016000000000006c00c000018000000b000000)
    (hweight : bitCount 180 (outsideMask word 0x300a6016000000000006c00c000018000000b000000) ≤ 1) :
    outsideMask word 0x300a6016000000000006c00c000018000000b000000 ∈ allowed555 := by
  exact outside_mem_of_search 8 180 10 rows555 lambdas555 0x41 0x300a6016000000000006c00c000018000000b000000 rhs555 1
    topEColumns topETransposeColumns tree555 allowed555 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked555 checked555
    hw (he.trans rhsChecked555) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 556. -/
noncomputable def lambdas556 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 556. -/
noncomputable def rhs556 : Nat := 0x900093648000948000000000049b000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked556 : reconX topRColumns 0x30116026000000000006c00c0000140000013000000 = rhs556 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 556. -/
theorem initialChecked556 : checkSearchInitial 8 180 10 rows556 lambdas556 0x41 0x30116026000000000006c00c0000140000013000000 rhs556 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 556 has a listed outside support. -/
theorem complete556 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30116026000000000006c00c0000140000013000000)
    (hweight : bitCount 180 (outsideMask word 0x30116026000000000006c00c0000140000013000000) ≤ 1) :
    outsideMask word 0x30116026000000000006c00c0000140000013000000 ∈ allowed556 := by
  exact outside_mem_of_search 8 180 10 rows556 lambdas556 0x41 0x30116026000000000006c00c0000140000013000000 rhs556 1
    topEColumns topETransposeColumns tree556 allowed556 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked556 checked556
    hw (he.trans rhsChecked556) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 557. -/
noncomputable def lambdas557 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000008000008040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000080000083000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 557. -/
noncomputable def rhs557 : Nat := 0xb40012b76000fe400001200001b240000240024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked557 : reconX topRColumns 0x30404000400000000900a802801c004003200200000 = rhs557 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 557. -/
theorem initialChecked557 : checkSearchInitial 8 180 13 rows557 lambdas557 0x4 0x30404000400000000900a802801c004003200200000 rhs557 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 557 has a listed outside support. -/
theorem complete557 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30404000400000000900a802801c004003200200000)
    (hweight : bitCount 180 (outsideMask word 0x30404000400000000900a802801c004003200200000) ≤ 1) :
    outsideMask word 0x30404000400000000900a802801c004003200200000 ∈ allowed557 := by
  exact outside_mem_of_search 8 180 13 rows557 lambdas557 0x4 0x30404000400000000900a802801c004003200200000 rhs557 1
    topEColumns topETransposeColumns tree557 allowed557 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked557 checked557
    hw (he.trans rhsChecked557) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 558. -/
noncomputable def lambdas558 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000008000000200000400000002000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000080000083000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 558. -/
noncomputable def rhs558 : Nat := 0xb40012b7600025200001200001b240000000024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked558 : reconX topRColumns 0x30406400000000000900a802801c002003200000000 = rhs558 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 558. -/
theorem initialChecked558 : checkSearchInitial 8 180 12 rows558 lambdas558 0x4 0x30406400000000000900a802801c002003200000000 rhs558 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 558 has a listed outside support. -/
theorem complete558 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30406400000000000900a802801c002003200000000)
    (hweight : bitCount 180 (outsideMask word 0x30406400000000000900a802801c002003200000000) ≤ 1) :
    outsideMask word 0x30406400000000000900a802801c002003200000000 ∈ allowed558 := by
  exact outside_mem_of_search 8 180 12 rows558 lambdas558 0x4 0x30406400000000000900a802801c002003200000000 rhs558 1
    topEColumns topETransposeColumns tree558 allowed558 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked558 checked558
    hw (he.trans rhsChecked558) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 559. -/
noncomputable def lambdas559 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000020000000000000440000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 559. -/
noncomputable def rhs559 : Nat := 0x240120120006db000012000000000000900000924000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked559 : reconX topRColumns 0x30c09009e000002000000400001b000000000800900 = rhs559 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 559. -/
theorem initialChecked559 : checkSearchInitial 8 180 10 rows559 lambdas559 0x40 0x30c09009e000002000000400001b000000000800900 rhs559 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 559 has a listed outside support. -/
theorem complete559 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30c09009e000002000000400001b000000000800900)
    (hweight : bitCount 180 (outsideMask word 0x30c09009e000002000000400001b000000000800900) ≤ 1) :
    outsideMask word 0x30c09009e000002000000400001b000000000800900 ∈ allowed559 := by
  exact outside_mem_of_search 8 180 10 rows559 lambdas559 0x40 0x30c09009e000002000000400001b000000000800900 rhs559 1
    topEColumns topETransposeColumns tree559 allowed559 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked559 checked559
    hw (he.trans rhsChecked559) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 560. -/
noncomputable def lambdas560 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000018000000600000600000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 560. -/
noncomputable def rhs560 : Nat := 0x120000006db000fc0000024900000000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked560 : reconX topRColumns 0x3100900000000000000fc000001b038004800000000 = rhs560 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 560. -/
theorem initialChecked560 : checkSearchInitial 8 180 15 rows560 lambdas560 0x1 0x3100900000000000000fc000001b038004800000000 rhs560 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 560 has a listed outside support. -/
theorem complete560 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3100900000000000000fc000001b038004800000000)
    (hweight : bitCount 180 (outsideMask word 0x3100900000000000000fc000001b038004800000000) ≤ 1) :
    outsideMask word 0x3100900000000000000fc000001b038004800000000 ∈ allowed560 := by
  exact outside_mem_of_search 8 180 15 rows560 lambdas560 0x1 0x3100900000000000000fc000001b038004800000000 rhs560 1
    topEColumns topETransposeColumns tree560 allowed560 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked560 checked560
    hw (he.trans rhsChecked560) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 561. -/
noncomputable def lambdas561 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000300000008000008200000000000000000400000000000000000000000038000000600000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 561. -/
noncomputable def rhs561 : Nat := 0x120000006db000900000024900024000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked561 : reconX topRColumns 0x3104100800000000000fc000001b020004804000000 = rhs561 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 561. -/
theorem initialChecked561 : checkSearchInitial 8 180 15 rows561 lambdas561 0x1 0x3104100800000000000fc000001b020004804000000 rhs561 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 561 has a listed outside support. -/
theorem complete561 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3104100800000000000fc000001b020004804000000)
    (hweight : bitCount 180 (outsideMask word 0x3104100800000000000fc000001b020004804000000) ≤ 1) :
    outsideMask word 0x3104100800000000000fc000001b020004804000000 ∈ allowed561 := by
  exact outside_mem_of_search 8 180 15 rows561 lambdas561 0x1 0x3104100800000000000fc000001b020004804000000 rhs561 1
    topEColumns topETransposeColumns tree561 allowed561 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked561 checked561
    hw (he.trans rhsChecked561) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 562. -/
noncomputable def lambdas562 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000030000000c400000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000008000000e00000400000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 562. -/
noncomputable def rhs562 : Nat := 0x36d80000fc0000480000009036d80000492000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked562 : reconX topRColumns 0x3200200000001200dc0540100008010001000030000 = rhs562 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 562. -/
theorem initialChecked562 : checkSearchInitial 8 180 12 rows562 lambdas562 0x9 0x3200200000001200dc0540100008010001000030000 rhs562 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 562 has a listed outside support. -/
theorem complete562 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3200200000001200dc0540100008010001000030000)
    (hweight : bitCount 180 (outsideMask word 0x3200200000001200dc0540100008010001000030000) ≤ 1) :
    outsideMask word 0x3200200000001200dc0540100008010001000030000 ∈ allowed562 := by
  exact outside_mem_of_search 8 180 12 rows562 lambdas562 0x9 0x3200200000001200dc0540100008010001000030000 rhs562 1
    topEColumns topETransposeColumns tree562 allowed562 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked562 checked562
    hw (he.trans rhsChecked562) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 563. -/
noncomputable def lambdas563 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000200000004000006000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000040000040200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000008000000c00000400000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 563. -/
noncomputable def rhs563 : Nat := 0x1b480000d80000480000009000000000fff000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked563 : reconX topRColumns 0x320020000000410048050006000001000100001b006 = rhs563 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 563. -/
theorem initialChecked563 : checkSearchInitial 8 180 13 rows563 lambdas563 0x10 0x320020000000410048050006000001000100001b006 rhs563 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 563 has a listed outside support. -/
theorem complete563 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x320020000000410048050006000001000100001b006)
    (hweight : bitCount 180 (outsideMask word 0x320020000000410048050006000001000100001b006) ≤ 1) :
    outsideMask word 0x320020000000410048050006000001000100001b006 ∈ allowed563 := by
  exact outside_mem_of_search 8 180 13 rows563 lambdas563 0x10 0x320020000000410048050006000001000100001b006 rhs563 1
    topEColumns topETransposeColumns tree563 allowed563 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked563 checked563
    hw (he.trans rhsChecked563) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 564. -/
noncomputable def lambdas564 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000400000600000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000038000000000000000000000000c00000800000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 564. -/
noncomputable def rhs564 : Nat := 0x12d80000d80000480000009036d80000fe4000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked564 : reconX topRColumns 0x3200200000005a00780500000000010001000028006 = rhs564 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 564. -/
theorem initialChecked564 : checkSearchInitial 8 180 14 rows564 lambdas564 0x21 0x3200200000005a00780500000000010001000028006 rhs564 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 564 has a listed outside support. -/
theorem complete564 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3200200000005a00780500000000010001000028006)
    (hweight : bitCount 180 (outsideMask word 0x3200200000005a00780500000000010001000028006) ≤ 1) :
    outsideMask word 0x3200200000005a00780500000000010001000028006 ∈ allowed564 := by
  exact outside_mem_of_search 8 180 14 rows564 lambdas564 0x21 0x3200200000005a00780500000000010001000028006 rhs564 1
    topEColumns topETransposeColumns tree564 allowed564 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked564 checked564
    hw (he.trans rhsChecked564) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 565. -/
noncomputable def lambdas565 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000200000004000006000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000c000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 565. -/
noncomputable def rhs565 : Nat := 0x9d80000d80000480000009024900000da4000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked565 : reconX topRColumns 0x3200200000006c001805000c0000010001000030006 = rhs565 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 565. -/
theorem initialChecked565 : checkSearchInitial 8 180 14 rows565 lambdas565 0x20 0x3200200000006c001805000c0000010001000030006 rhs565 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 565 has a listed outside support. -/
theorem complete565 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3200200000006c001805000c0000010001000030006)
    (hweight : bitCount 180 (outsideMask word 0x3200200000006c001805000c0000010001000030006) ≤ 1) :
    outsideMask word 0x3200200000006c001805000c0000010001000030006 ∈ allowed565 := by
  exact outside_mem_of_search 8 180 14 rows565 lambdas565 0x20 0x3200200000006c001805000c0000010001000030006 rhs565 1
    topEColumns topETransposeColumns tree565 allowed565 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked565 checked565
    hw (he.trans rhsChecked565) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 566. -/
noncomputable def lambdas566 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000c0000001000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000038000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 566. -/
noncomputable def rhs566 : Nat := 0xb400126c000049200001200001b0000000004b690002d

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked566 : reconX topRColumns 0x3200600000000000650068028002002003000000003 = rhs566 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 566. -/
theorem initialChecked566 : checkSearchInitial 8 180 10 rows566 lambdas566 0x28 0x3200600000000000650068028002002003000000003 rhs566 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 566 has a listed outside support. -/
theorem complete566 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3200600000000000650068028002002003000000003)
    (hweight : bitCount 180 (outsideMask word 0x3200600000000000650068028002002003000000003) ≤ 1) :
    outsideMask word 0x3200600000000000650068028002002003000000003 ∈ allowed566 := by
  exact outside_mem_of_search 8 180 10 rows566 lambdas566 0x28 0x3200600000000000650068028002002003000000003 rhs566 1
    topEColumns topETransposeColumns tree566 allowed566 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked566 checked566
    hw (he.trans rhsChecked566) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 567. -/
noncomputable def lambdas567 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000c000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 567. -/
noncomputable def rhs567 : Nat := 0x3fd80036240000480000009000009000492000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked567 : reconX topRColumns 0x3201000200000000fc0540140008020001001000000 = rhs567 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 567. -/
theorem initialChecked567 : checkSearchInitial 8 180 11 rows567 lambdas567 0x4 0x3201000200000000fc0540140008020001001000000 rhs567 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 567 has a listed outside support. -/
theorem complete567 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3201000200000000fc0540140008020001001000000)
    (hweight : bitCount 180 (outsideMask word 0x3201000200000000fc0540140008020001001000000) ≤ 1) :
    outsideMask word 0x3201000200000000fc0540140008020001001000000 ∈ allowed567 := by
  exact outside_mem_of_search 8 180 11 rows567 lambdas567 0x4 0x3201000200000000fc0540140008020001001000000 rhs567 1
    topEColumns topETransposeColumns tree567 allowed567 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked567 checked567
    hw (he.trans rhsChecked567) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 568. -/
noncomputable def lambdas568 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000020000000e00000201000000000000000000000000000000000000000000000002000000080000020000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 568. -/
noncomputable def rhs568 : Nat := 0x1bd800364800004800000090000090006c000093f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked568 : reconX topRColumns 0x3201000200004800100580040010020001001018003 = rhs568 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 568. -/
theorem initialChecked568 : checkSearchInitial 8 180 11 rows568 lambdas568 0x8 0x3201000200004800100580040010020001001018003 rhs568 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 568 has a listed outside support. -/
theorem complete568 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3201000200004800100580040010020001001018003)
    (hweight : bitCount 180 (outsideMask word 0x3201000200004800100580040010020001001018003) ≤ 1) :
    outsideMask word 0x3201000200004800100580040010020001001018003 ∈ allowed568 := by
  exact outside_mem_of_search 8 180 11 rows568 lambdas568 0x8 0x3201000200004800100580040010020001001018003 rhs568 1
    topEColumns topETransposeColumns tree568 allowed568 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked568 checked568
    hw (he.trans rhsChecked568) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 569. -/
noncomputable def lambdas569 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000020000000e00000201000000000000000000000000000000000000000000000002000000080000020000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000c000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 569. -/
noncomputable def rhs569 : Nat := 0x1bd80036000000480000009000009000fe4000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked569 : reconX topRColumns 0x3201000200004800580500040000020001001018006 = rhs569 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 569. -/
theorem initialChecked569 : checkSearchInitial 8 180 13 rows569 lambdas569 0x10 0x3201000200004800580500040000020001001018006 rhs569 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 569 has a listed outside support. -/
theorem complete569 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3201000200004800580500040000020001001018006)
    (hweight : bitCount 180 (outsideMask word 0x3201000200004800580500040000020001001018006) ≤ 1) :
    outsideMask word 0x3201000200004800580500040000020001001018006 ∈ allowed569 := by
  exact outside_mem_of_search 8 180 13 rows569 lambdas569 0x10 0x3201000200004800580500040000020001001018006 rhs569 1
    topEColumns topETransposeColumns tree569 allowed569 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked569 checked569
    hw (he.trans rhsChecked569) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 570. -/
noncomputable def lambdas570 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000080000080000001000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000010e00000a000002000000000000000000040000000000000000000000000000000000000000000000000000000800000c00000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 570. -/
noncomputable def rhs570 : Nat := 0x369000004800002400000120249000006d2000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked570 : reconX topRColumns 0x34004000000024002c0280100030008002000028003 = rhs570 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 570. -/
theorem initialChecked570 : checkSearchInitial 8 180 12 rows570 lambdas570 0x3 0x34004000000024002c0280100030008002000028003 rhs570 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 570 has a listed outside support. -/
theorem complete570 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x34004000000024002c0280100030008002000028003)
    (hweight : bitCount 180 (outsideMask word 0x34004000000024002c0280100030008002000028003) ≤ 1) :
    outsideMask word 0x34004000000024002c0280100030008002000028003 ∈ allowed570 := by
  exact outside_mem_of_search 8 180 12 rows570 lambdas570 0x3 0x34004000000024002c0280100030008002000028003 rhs570 1
    topEColumns topETransposeColumns tree570 allowed570 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked570 checked570
    hw (he.trans rhsChecked570) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 571. -/
noncomputable def lambdas571 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000028000000c400000000000000000000000000000000a0000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000010000000e00000200000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 571. -/
noncomputable def rhs571 : Nat := 0x36900000d800002400000120249000006d2000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked571 : reconX topRColumns 0x3400400000002400bc0380100010008002000028000 = rhs571 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 571. -/
theorem initialChecked571 : checkSearchInitial 8 180 12 rows571 lambdas571 0x8 0x3400400000002400bc0380100010008002000028000 rhs571 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 571 has a listed outside support. -/
theorem complete571 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3400400000002400bc0380100010008002000028000)
    (hweight : bitCount 180 (outsideMask word 0x3400400000002400bc0380100010008002000028000) ≤ 1) :
    outsideMask word 0x3400400000002400bc0380100010008002000028000 ∈ allowed571 := by
  exact outside_mem_of_search 8 180 12 rows571 lambdas571 0x8 0x3400400000002400bc0380100010008002000028000 rhs571 1
    topEColumns topETransposeColumns tree571 allowed571 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked571 checked571
    hw (he.trans rhsChecked571) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 572. -/
noncomputable def lambdas572 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000000000a00000000000000000000000000000021000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 572. -/
noncomputable def rhs572 : Nat := 0x900000d80000240000012000000000252000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked572 : reconX topRColumns 0x34004000000048007c0380080010008002000018000 = rhs572 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 572. -/
theorem initialChecked572 : checkSearchInitial 8 180 10 rows572 lambdas572 0x1 0x34004000000048007c0380080010008002000018000 rhs572 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 572 has a listed outside support. -/
theorem complete572 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x34004000000048007c0380080010008002000018000)
    (hweight : bitCount 180 (outsideMask word 0x34004000000048007c0380080010008002000018000) ≤ 1) :
    outsideMask word 0x34004000000048007c0380080010008002000018000 ∈ allowed572 := by
  exact outside_mem_of_search 8 180 10 rows572 lambdas572 0x1 0x34004000000048007c0380080010008002000018000 rhs572 1
    topEColumns topETransposeColumns tree572 allowed572 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked572 checked572
    hw (he.trans rhsChecked572) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 573. -/
noncomputable def lambdas573 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000003800000088000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000a00000000000000000000000000000002000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 573. -/
noncomputable def rhs573 : Nat := 0x12900000d80000240000012024900000012000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked573 : reconX topRColumns 0x3400400000006c003c0380000010008002000030000 = rhs573 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 573. -/
theorem initialChecked573 : checkSearchInitial 8 180 12 rows573 lambdas573 0x4 0x3400400000006c003c0380000010008002000030000 rhs573 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 573 has a listed outside support. -/
theorem complete573 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3400400000006c003c0380000010008002000030000)
    (hweight : bitCount 180 (outsideMask word 0x3400400000006c003c0380000010008002000030000) ≤ 1) :
    outsideMask word 0x3400400000006c003c0380000010008002000030000 ∈ allowed573 := by
  exact outside_mem_of_search 8 180 12 rows573 lambdas573 0x4 0x3400400000006c003c0380000010008002000030000 rhs573 1
    topEColumns topETransposeColumns tree573 allowed573 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked573 checked573
    hw (he.trans rhsChecked573) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 574. -/
noncomputable def lambdas574 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000030000000000000880

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 574. -/
noncomputable def rhs574 : Nat := 0x1b900000900000240000012012480000936000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked574 : reconX topRColumns 0x3400400000007e00540300040000008002000000005 = rhs574 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 574. -/
theorem initialChecked574 : checkSearchInitial 8 180 12 rows574 lambdas574 0x21 0x3400400000007e00540300040000008002000000005 rhs574 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 574 has a listed outside support. -/
theorem complete574 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3400400000007e00540300040000008002000000005)
    (hweight : bitCount 180 (outsideMask word 0x3400400000007e00540300040000008002000000005) ≤ 1) :
    outsideMask word 0x3400400000007e00540300040000008002000000005 ∈ allowed574 := by
  exact outside_mem_of_search 8 180 12 rows574 lambdas574 0x21 0x3400400000007e00540300040000008002000000005 rhs574 1
    topEColumns topETransposeColumns tree574 allowed574 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked574 checked574
    hw (he.trans rhsChecked574) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 575. -/
noncomputable def lambdas575 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000380000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000a00000e08000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 575. -/
noncomputable def rhs575 : Nat := 0xd8001248000048900000900001b0000000004a4d8003f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked575 : reconX topRColumns 0x34006000000000006880b0030001001003000000003 = rhs575 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 575. -/
theorem initialChecked575 : checkSearchInitial 8 180 10 rows575 lambdas575 0x11 0x34006000000000006880b0030001001003000000003 rhs575 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 575 has a listed outside support. -/
theorem complete575 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x34006000000000006880b0030001001003000000003)
    (hweight : bitCount 180 (outsideMask word 0x34006000000000006880b0030001001003000000003) ≤ 1) :
    outsideMask word 0x34006000000000006880b0030001001003000000003 ∈ allowed575 := by
  exact outside_mem_of_search 8 180 10 rows575 lambdas575 0x11 0x34006000000000006880b0030001001003000000003 rhs575 1
    topEColumns topETransposeColumns tree575 allowed575 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked575 checked575
    hw (he.trans rhsChecked575) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 576. -/
noncomputable def lambdas576 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 576. -/
noncomputable def rhs576 : Nat := 0x24900024480000000000012000012000492000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked576 : reconX topRColumns 0x3402000400000000fc0380180010020002002000000 = rhs576 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 576. -/
theorem initialChecked576 : checkSearchInitial 8 180 11 rows576 lambdas576 0x4 0x3402000400000000fc0380180010020002002000000 rhs576 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 576 has a listed outside support. -/
theorem complete576 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3402000400000000fc0380180010020002002000000)
    (hweight : bitCount 180 (outsideMask word 0x3402000400000000fc0380180010020002002000000) ≤ 1) :
    outsideMask word 0x3402000400000000fc0380180010020002002000000 ∈ allowed576 := by
  exact outside_mem_of_search 8 180 11 rows576 lambdas576 0x4 0x3402000400000000fc0380180010020002002000000 rhs576 1
    topEColumns topETransposeColumns tree576 allowed576 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked576 checked576
    hw (he.trans rhsChecked576) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 577. -/
noncomputable def lambdas577 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000380000000000000000000000000000001000000000000000000000000000000000e00000000000000000000000000000004000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 577. -/
noncomputable def rhs577 : Nat := 0x1248003690000000000001b000009000492000009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked577 : reconX topRColumns 0x36014002000000006c00c0000000030003001000003 = rhs577 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 577. -/
theorem initialChecked577 : checkSearchInitial 8 180 10 rows577 lambdas577 0x3 0x36014002000000006c00c0000000030003001000003 rhs577 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 577 has a listed outside support. -/
theorem complete577 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x36014002000000006c00c0000000030003001000003)
    (hweight : bitCount 180 (outsideMask word 0x36014002000000006c00c0000000030003001000003) ≤ 1) :
    outsideMask word 0x36014002000000006c00c0000000030003001000003 ∈ allowed577 := by
  exact outside_mem_of_search 8 180 10 rows577 lambdas577 0x3 0x36014002000000006c00c0000000030003001000003 rhs577 1
    topEColumns topETransposeColumns tree577 allowed577 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked577 checked577
    hw (he.trans rhsChecked577) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 578. -/
noncomputable def lambdas578 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000380000000000000000000000000000001000000000000000000000000000000000e00000000000000000000000000000004000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 578. -/
noncomputable def rhs578 : Nat := 0x12480024d8000024000001b000012000492000009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked578 : reconX topRColumns 0x36022004000000006c00c0000000028003002000003 = rhs578 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 578. -/
theorem initialChecked578 : checkSearchInitial 8 180 10 rows578 lambdas578 0x3 0x36022004000000006c00c0000000028003002000003 rhs578 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 578 has a listed outside support. -/
theorem complete578 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x36022004000000006c00c0000000028003002000003)
    (hweight : bitCount 180 (outsideMask word 0x36022004000000006c00c0000000028003002000003) ≤ 1) :
    outsideMask word 0x36022004000000006c00c0000000028003002000003 ∈ allowed578 := by
  exact outside_mem_of_search 8 180 10 rows578 lambdas578 0x3 0x36022004000000006c00c0000000028003002000003 rhs578 1
    topEColumns topETransposeColumns tree578 allowed578 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked578 checked578
    hw (he.trans rhsChecked578) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 579. -/
noncomputable def lambdas579 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000028000008000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000002380000000000000000000000000000201000000000000000000000000000000000600000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 579. -/
noncomputable def rhs579 : Nat := 0x12000009000000fc000002400000003691200049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked579 : reconX topRColumns 0x38008000000000014c0d00000040038004000000033 = rhs579 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 579. -/
theorem initialChecked579 : checkSearchInitial 8 180 14 rows579 lambdas579 0x10 0x38008000000000014c0d00000040038004000000033 rhs579 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 579 has a listed outside support. -/
theorem complete579 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38008000000000014c0d00000040038004000000033)
    (hweight : bitCount 180 (outsideMask word 0x38008000000000014c0d00000040038004000000033) ≤ 1) :
    outsideMask word 0x38008000000000014c0d00000040038004000000033 ∈ allowed579 := by
  exact outside_mem_of_search 8 180 14 rows579 lambdas579 0x10 0x38008000000000014c0d00000040038004000000033 rhs579 1
    topEColumns topETransposeColumns tree579 allowed579 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked579 checked579
    hw (he.trans rhsChecked579) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 580. -/
noncomputable def lambdas580 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000300000100000000800000000000000000000000000000000000000000000000010000010600000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000043800000000000000000000000000002010000000000000000000000000000000006000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 580. -/
noncomputable def rhs580 : Nat := 0x12000012000000fc0000024000000024d920006db

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked580 : reconX topRColumns 0x38008000000000022c0b0000008003800400000002b = rhs580 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 580. -/
theorem initialChecked580 : checkSearchInitial 8 180 14 rows580 lambdas580 0x604 0x38008000000000022c0b0000008003800400000002b rhs580 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 580 has a listed outside support. -/
theorem complete580 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38008000000000022c0b0000008003800400000002b)
    (hweight : bitCount 180 (outsideMask word 0x38008000000000022c0b0000008003800400000002b) ≤ 1) :
    outsideMask word 0x38008000000000022c0b0000008003800400000002b ∈ allowed580 := by
  exact outside_mem_of_search 8 180 14 rows580 lambdas580 0x604 0x38008000000000022c0b0000008003800400000002b rhs580 1
    topEColumns topETransposeColumns tree580 allowed580 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked580 checked580
    hw (he.trans rhsChecked580) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 581. -/
noncomputable def lambdas581 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000003000001000000008000000000000000000000000000000000000000000000000280000080000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000060000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 581. -/
noncomputable def rhs581 : Nat := 0x1200001b000000fc00000240000000120120006db

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked581 : reconX topRColumns 0x38008000000000030c09000000c003800400000001b = rhs581 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 581. -/
theorem initialChecked581 : checkSearchInitial 8 180 15 rows581 lambdas581 0x800 0x38008000000000030c09000000c003800400000001b rhs581 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 581 has a listed outside support. -/
theorem complete581 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38008000000000030c09000000c003800400000001b)
    (hweight : bitCount 180 (outsideMask word 0x38008000000000030c09000000c003800400000001b) ≤ 1) :
    outsideMask word 0x38008000000000030c09000000c003800400000001b ∈ allowed581 := by
  exact outside_mem_of_search 8 180 15 rows581 lambdas581 0x800 0x38008000000000030c09000000c003800400000001b rhs581 1
    topEColumns topETransposeColumns tree581 allowed581 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked581 checked581
    hw (he.trans rhsChecked581) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 582. -/
noncomputable def lambdas582 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000038600000000000000000000000000000804000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000010000000e00000200000000000000000000000001 (Nat.shiftLeft 0x800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 582. -/
noncomputable def rhs582 : Nat := 0x12000036900000fc0000024000009000db6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked582 : reconX topRColumns 0x3801a00200000000240f80000010008004001000006 = rhs582 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 582. -/
theorem initialChecked582 : checkSearchInitial 8 180 18 rows582 lambdas582 0x9 0x3801a00200000000240f80000010008004001000006 rhs582 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 582 has a listed outside support. -/
theorem complete582 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3801a00200000000240f80000010008004001000006)
    (hweight : bitCount 180 (outsideMask word 0x3801a00200000000240f80000010008004001000006) ≤ 1) :
    outsideMask word 0x3801a00200000000240f80000010008004001000006 ∈ allowed582 := by
  exact outside_mem_of_search 8 180 18 rows582 lambdas582 0x9 0x3801a00200000000240f80000010008004001000006 rhs582 1
    topEColumns topETransposeColumns tree582 allowed582 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked582 checked582
    hw (he.trans rhsChecked582) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 583. -/
noncomputable def lambdas583 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000003860000000000000000000000000000080400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000030000000000000000000000000000000040 (Nat.shiftLeft 0x80000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 583. -/
noncomputable def rhs583 : Nat := 0x12000036fc0000fc000002400000900092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked583 : reconX topRColumns 0x3801a00200000000480f40000008008004001000005 = rhs583 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 583. -/
theorem initialChecked583 : checkSearchInitial 8 180 17 rows583 lambdas583 0x4 0x3801a00200000000480f40000008008004001000005 rhs583 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 583 has a listed outside support. -/
theorem complete583 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3801a00200000000480f40000008008004001000005)
    (hweight : bitCount 180 (outsideMask word 0x3801a00200000000480f40000008008004001000005) ≤ 1) :
    outsideMask word 0x3801a00200000000480f40000008008004001000005 ∈ allowed583 := by
  exact outside_mem_of_search 8 180 17 rows583 lambdas583 0x4 0x3801a00200000000480f40000008008004001000005 rhs583 1
    topEColumns topETransposeColumns tree583 allowed583 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked583 checked583
    hw (he.trans rhsChecked583) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 584. -/
noncomputable def lambdas584 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000020000000200000e00000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000038000000000000000000000000000000100000000000000000000000000000000060000000000000000000000000000000400000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 584. -/
noncomputable def rhs584 : Nat := 0x12000036d80000fc000002400000900049200049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked584 : reconX topRColumns 0x3801a002000000006c0f00000000008004001000003 = rhs584 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 584. -/
theorem initialChecked584 : checkSearchInitial 8 180 12 rows584 lambdas584 0x8 0x3801a002000000006c0f00000000008004001000003 rhs584 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 584 has a listed outside support. -/
theorem complete584 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3801a002000000006c0f00000000008004001000003)
    (hweight : bitCount 180 (outsideMask word 0x3801a002000000006c0f00000000008004001000003) ≤ 1) :
    outsideMask word 0x3801a002000000006c0f00000000008004001000003 ∈ allowed584 := by
  exact outside_mem_of_search 8 180 12 rows584 lambdas584 0x8 0x3801a002000000006c0f00000000008004001000003 rhs584 1
    topEColumns topETransposeColumns tree584 allowed584 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked584 checked584
    hw (he.trans rhsChecked584) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 585. -/
noncomputable def lambdas585 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000038600000000000000000000000000000804000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000280000000000000000000000000000000800000000000000000000000008000000e00000400000000000000000000000002 (Nat.shiftLeft 0x800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 585. -/
noncomputable def rhs585 : Nat := 0x12000024b40000d8000002400001200092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked585 : reconX topRColumns 0x3802c00400000000480f40000008010004002000005 = rhs585 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 585. -/
theorem initialChecked585 : checkSearchInitial 8 180 18 rows585 lambdas585 0x8 0x3802c00400000000480f40000008010004002000005 rhs585 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 585 has a listed outside support. -/
theorem complete585 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3802c00400000000480f40000008010004002000005)
    (hweight : bitCount 180 (outsideMask word 0x3802c00400000000480f40000008010004002000005) ≤ 1) :
    outsideMask word 0x3802c00400000000480f40000008010004002000005 ∈ allowed585 := by
  exact outside_mem_of_search 8 180 18 rows585 lambdas585 0x8 0x3802c00400000000480f40000008010004002000005 rhs585 1
    topEColumns topETransposeColumns tree585 allowed585 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked585 checked585
    hw (he.trans rhsChecked585) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 586. -/
noncomputable def lambdas586 : Nat := (Nat.lor 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000038e0000000000000000000000000000020100000000000000000000000000000000000180000000000000000000000000000001000000000000000000000000000000030000000800000820000000000000000040 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 586. -/
noncomputable def rhs586 : Nat := 0x12000000fc0000900000024000024000000000489

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked586 : reconX topRColumns 0x3804000800000000900ec0000038020004004000003 = rhs586 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 586. -/
theorem initialChecked586 : checkSearchInitial 8 180 19 rows586 lambdas586 0x4 0x3804000800000000900ec0000038020004004000003 rhs586 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 586 has a listed outside support. -/
theorem complete586 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3804000800000000900ec0000038020004004000003)
    (hweight : bitCount 180 (outsideMask word 0x3804000800000000900ec0000038020004004000003) ≤ 1) :
    outsideMask word 0x3804000800000000900ec0000038020004004000003 ∈ allowed586 := by
  exact outside_mem_of_search 8 180 19 rows586 lambdas586 0x4 0x3804000800000000900ec0000038020004004000003 rhs586 1
    topEColumns topETransposeColumns tree586 allowed586 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked586 checked586
    hw (he.trans rhsChecked586) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 587. -/
noncomputable def lambdas587 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000001800000000000000000000000000000010000000000000000000000000000000280000008000008200000000000000000800000000000000000000000000000030000000800000820000000000000000040 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 587. -/
noncomputable def rhs587 : Nat := 0x12000000b40000900000024000024000924000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked587 : reconX topRColumns 0x3804000800000000d80e40000028020004004000006 = rhs587 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 587. -/
theorem initialChecked587 : checkSearchInitial 8 180 19 rows587 lambdas587 0x2 0x3804000800000000d80e40000028020004004000006 rhs587 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 587 has a listed outside support. -/
theorem complete587 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3804000800000000d80e40000028020004004000006)
    (hweight : bitCount 180 (outsideMask word 0x3804000800000000d80e40000028020004004000006) ≤ 1) :
    outsideMask word 0x3804000800000000d80e40000028020004004000006 ∈ allowed587 := by
  exact outside_mem_of_search 8 180 19 rows587 lambdas587 0x2 0x3804000800000000d80e40000028020004004000006 rhs587 1
    topEColumns topETransposeColumns tree587 allowed587 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked587 checked587
    hw (he.trans rhsChecked587) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 588. -/
noncomputable def lambdas588 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000002380000004000000000000000000000208000000040000000000000000000000000400000c00000820000000000000000000000001 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 588. -/
noncomputable def rhs588 : Nat := 0x12000009480000900000024000024036036000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked588 : reconX topRColumns 0x3804000800000001040d80000050020004004000036 = rhs588 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 588. -/
theorem initialChecked588 : checkSearchInitial 8 180 18 rows588 lambdas588 0x2 0x3804000800000001040d80000050020004004000036 rhs588 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 588 has a listed outside support. -/
theorem complete588 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3804000800000001040d80000050020004004000036)
    (hweight : bitCount 180 (outsideMask word 0x3804000800000001040d80000050020004004000036) ≤ 1) :
    outsideMask word 0x3804000800000001040d80000050020004004000036 ∈ allowed588 := by
  exact outside_mem_of_search 8 180 18 rows588 lambdas588 0x2 0x3804000800000001040d80000050020004004000036 rhs588 1
    topEColumns topETransposeColumns tree588 allowed588 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked588 checked588
    hw (he.trans rhsChecked588) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 589. -/
noncomputable def lambdas589 : Nat := (Nat.lor 0x4000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000200000a000008200000000000000000000000020000000000000000000000000400000c00000820000000000000000000000001 (Nat.shiftLeft 0x80000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 589. -/
noncomputable def rhs589 : Nat := 0x120000096c0000900000024000024036d80000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked589 : reconX topRColumns 0x3804000800000001200dc0000058020004004000030 = rhs589 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 589. -/
theorem initialChecked589 : checkSearchInitial 8 180 17 rows589 lambdas589 0x2 0x3804000800000001200dc0000058020004004000030 rhs589 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 589 has a listed outside support. -/
theorem complete589 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3804000800000001200dc0000058020004004000030)
    (hweight : bitCount 180 (outsideMask word 0x3804000800000001200dc0000058020004004000030) ≤ 1) :
    outsideMask word 0x3804000800000001200dc0000058020004004000030 ∈ allowed589 := by
  exact outside_mem_of_search 8 180 17 rows589 lambdas589 0x2 0x3804000800000001200dc0000058020004004000030 rhs589 1
    topEColumns topETransposeColumns tree589 allowed589 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked589 checked589
    hw (he.trans rhsChecked589) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 590. -/
noncomputable def lambdas590 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000002380000000000000000000000000000201000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000300000008000008200000000000000000400000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 590. -/
noncomputable def rhs590 : Nat := 0x1200000900000090000002400002403691200049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked590 : reconX topRColumns 0x38040008000000014c0d00000040020004004000033 = rhs590 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 590. -/
theorem initialChecked590 : checkSearchInitial 8 180 16 rows590 lambdas590 0x10 0x38040008000000014c0d00000040020004004000033 rhs590 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 590 has a listed outside support. -/
theorem complete590 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38040008000000014c0d00000040020004004000033)
    (hweight : bitCount 180 (outsideMask word 0x38040008000000014c0d00000040020004004000033) ≤ 1) :
    outsideMask word 0x38040008000000014c0d00000040020004004000033 ∈ allowed590 := by
  exact outside_mem_of_search 8 180 16 rows590 lambdas590 0x10 0x38040008000000014c0d00000040020004004000033 rhs590 1
    topEColumns topETransposeColumns tree590 allowed590 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked590 checked590
    hw (he.trans rhsChecked590) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 591. -/
noncomputable def lambdas591 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000002000000000000044000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000382000380000008200000000000000000000000800000000000000000000000000200000a00000820000000000000000000000002 (Nat.shiftLeft 0x800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 591. -/
noncomputable def rhs591 : Nat := 0x120000122400009000000240000240240240006db

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked591 : reconX topRColumns 0x3804000800000002080b4000008802000400400002d = rhs591 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 591. -/
theorem initialChecked591 : checkSearchInitial 8 180 18 rows591 lambdas591 0x1 0x3804000800000002080b4000008802000400400002d rhs591 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 591 has a listed outside support. -/
theorem complete591 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3804000800000002080b4000008802000400400002d)
    (hweight : bitCount 180 (outsideMask word 0x3804000800000002080b4000008802000400400002d) ≤ 1) :
    outsideMask word 0x3804000800000002080b4000008802000400400002d ∈ allowed591 := by
  exact outside_mem_of_search 8 180 18 rows591 lambdas591 0x1 0x3804000800000002080b4000008802000400400002d rhs591 1
    topEColumns topETransposeColumns tree591 allowed591 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked591 checked591
    hw (he.trans rhsChecked591) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 592. -/
noncomputable def lambdas592 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000280000008000008200000000000000000800000000000000000000000400000030000000800000820000000008000000040 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 592. -/
noncomputable def rhs592 : Nat := 0x12000012000000900000024000024024d920006db

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked592 : reconX topRColumns 0x38040008000000022c0b0000008002000400400002b = rhs592 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 592. -/
theorem initialChecked592 : checkSearchInitial 8 180 18 rows592 lambdas592 0x2 0x38040008000000022c0b0000008002000400400002b rhs592 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 592 has a listed outside support. -/
theorem complete592 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38040008000000022c0b0000008002000400400002b)
    (hweight : bitCount 180 (outsideMask word 0x38040008000000022c0b0000008002000400400002b) ≤ 1) :
    outsideMask word 0x38040008000000022c0b0000008002000400400002b ∈ allowed592 := by
  exact outside_mem_of_search 8 180 18 rows592 lambdas592 0x2 0x38040008000000022c0b0000008002000400400002b rhs592 1
    topEColumns topETransposeColumns tree592 allowed592 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked592 checked592
    hw (he.trans rhsChecked592) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 593. -/
noncomputable def lambdas593 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000002000000000000044000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000280000008000008200000000000000000800000000000000000000000400000030000000800000820000000008000000040 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 593. -/
noncomputable def rhs593 : Nat := 0x120000126c00009000000240000240249000006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked593 : reconX topRColumns 0x3804000800000002400bc0000098020004004000028 = rhs593 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 593. -/
theorem initialChecked593 : checkSearchInitial 8 180 19 rows593 lambdas593 0x2 0x3804000800000002400bc0000098020004004000028 rhs593 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 593 has a listed outside support. -/
theorem complete593 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3804000800000002400bc0000098020004004000028)
    (hweight : bitCount 180 (outsideMask word 0x3804000800000002400bc0000098020004004000028) ≤ 1) :
    outsideMask word 0x3804000800000002400bc0000098020004004000028 ∈ allowed593 := by
  exact outside_mem_of_search 8 180 19 rows593 lambdas593 0x2 0x3804000800000002400bc0000098020004004000028 rhs593 1
    topEColumns topETransposeColumns tree593 allowed593 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked593 checked593
    hw (he.trans rhsChecked593) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 594. -/
noncomputable def lambdas594 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000038000011000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000030000010000000400000800000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 594. -/
noncomputable def rhs594 : Nat := 0x1200001b0000009000000240000240120120006db

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked594 : reconX topRColumns 0x38040008000000030c09000000c002000400400001b = rhs594 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 594. -/
theorem initialChecked594 : checkSearchInitial 8 180 14 rows594 lambdas594 0x208 0x38040008000000030c09000000c002000400400001b rhs594 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 594 has a listed outside support. -/
theorem complete594 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38040008000000030c09000000c002000400400001b)
    (hweight : bitCount 180 (outsideMask word 0x38040008000000030c09000000c002000400400001b) ≤ 1) :
    outsideMask word 0x38040008000000030c09000000c002000400400001b ∈ allowed594 := by
  exact outside_mem_of_search 8 180 14 rows594 lambdas594 0x208 0x38040008000000030c09000000c002000400400001b rhs594 1
    topEColumns topETransposeColumns tree594 allowed594 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked594 checked594
    hw (he.trans rhsChecked594) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 595. -/
noncomputable def lambdas595 : Nat := (Nat.lor 0x4000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000180000000000000000000000000000001000000000000000000000000000200000a000008200000000000000000000000020000000000000000000000000400000c00000820000000000000000000000001 (Nat.shiftLeft 0x80000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 595. -/
noncomputable def rhs595 : Nat := 0x120000246c0000900000024000024000000000252

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked595 : reconX topRColumns 0x38040008000000048007c0000118020004004000018 = rhs595 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 595. -/
theorem initialChecked595 : checkSearchInitial 8 180 17 rows595 lambdas595 0x2 0x38040008000000048007c0000118020004004000018 rhs595 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 595 has a listed outside support. -/
theorem complete595 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x38040008000000048007c0000118020004004000018)
    (hweight : bitCount 180 (outsideMask word 0x38040008000000048007c0000118020004004000018) ≤ 1) :
    outsideMask word 0x38040008000000048007c0000118020004004000018 ∈ allowed595 := by
  exact outside_mem_of_search 8 180 17 rows595 lambdas595 0x2 0x38040008000000048007c0000118020004004000018 rhs595 1
    topEColumns topETransposeColumns tree595 allowed595 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked595 checked595
    hw (he.trans rhsChecked595) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 596. -/
noncomputable def lambdas596 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000003844000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000020400000c00000e20000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 596. -/
noncomputable def rhs596 : Nat := 0x12000036b4000090000002400002d000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked596 : reconX topRColumns 0x3805200a00000000000fc0000018010004005000000 = rhs596 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 596. -/
theorem initialChecked596 : checkSearchInitial 8 180 15 rows596 lambdas596 0x100 0x3805200a00000000000fc0000018010004005000000 rhs596 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 596 has a listed outside support. -/
theorem complete596 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3805200a00000000000fc0000018010004005000000)
    (hweight : bitCount 180 (outsideMask word 0x3805200a00000000000fc0000018010004005000000) ≤ 1) :
    outsideMask word 0x3805200a00000000000fc0000018010004005000000 ∈ allowed596 := by
  exact outside_mem_of_search 8 180 15 rows596 lambdas596 0x100 0x3805200a00000000000fc0000018010004005000000 rhs596 1
    topEColumns topETransposeColumns tree596 allowed596 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked596 checked596
    hw (he.trans rhsChecked596) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 597. -/
noncomputable def lambdas597 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000003844000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000018400000a00000e20000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 597. -/
noncomputable def rhs597 : Nat := 0x12000024fc0000b40000024000036000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked597 : reconX topRColumns 0x3806400c00000000000fc0000018008004006000000 = rhs597 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 597. -/
theorem initialChecked597 : checkSearchInitial 8 180 15 rows597 lambdas597 0x100 0x3806400c00000000000fc0000018008004006000000 rhs597 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 597 has a listed outside support. -/
theorem complete597 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3806400c00000000000fc0000018008004006000000)
    (hweight : bitCount 180 (outsideMask word 0x3806400c00000000000fc0000018008004006000000) ≤ 1) :
    outsideMask word 0x3806400c00000000000fc0000018008004006000000 ∈ allowed597 := by
  exact outside_mem_of_search 8 180 15 rows597 lambdas597 0x100 0x3806400c00000000000fc0000018008004006000000 rhs597 1
    topEColumns topETransposeColumns tree597 allowed597 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked597 checked597
    hw (he.trans rhsChecked597) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 598. -/
noncomputable def lambdas598 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 598. -/
noncomputable def rhs598 : Nat := 0x240120120006c0000009000000900000000000924000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked598 : reconX topRColumns 0x39c01008e0000020000004000018003000800000900 = rhs598 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 598. -/
theorem initialChecked598 : checkSearchInitial 8 180 10 rows598 lambdas598 0x20 0x39c01008e0000020000004000018003000800000900 rhs598 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 598 has a listed outside support. -/
theorem complete598 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x39c01008e0000020000004000018003000800000900)
    (hweight : bitCount 180 (outsideMask word 0x39c01008e0000020000004000018003000800000900) ≤ 1) :
    outsideMask word 0x39c01008e0000020000004000018003000800000900 ∈ allowed598 := by
  exact outside_mem_of_search 8 180 10 rows598 lambdas598 0x20 0x39c01008e0000020000004000018003000800000900 rhs598 1
    topEColumns topETransposeColumns tree598 allowed598 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked598 checked598
    hw (he.trans rhsChecked598) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 599. -/
noncomputable def lambdas599 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000008000020000000400000410000000000000000040 (Nat.shiftLeft 0x100000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 599. -/
noncomputable def rhs599 : Nat := 0x3f900024480000900000036000012000000000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked599 : reconX topRColumns 0x3c02800400000000900a40140010000006002000003 = rhs599 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 599. -/
theorem initialChecked599 : checkSearchInitial 8 180 17 rows599 lambdas599 0x1 0x3c02800400000000900a40140010000006002000003 rhs599 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 599 has a listed outside support. -/
theorem complete599 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3c02800400000000900a40140010000006002000003)
    (hweight : bitCount 180 (outsideMask word 0x3c02800400000000900a40140010000006002000003) ≤ 1) :
    outsideMask word 0x3c02800400000000900a40140010000006002000003 ∈ allowed599 := by
  exact outside_mem_of_search 8 180 17 rows599 lambdas599 0x1 0x3c02800400000000900a40140010000006002000003 rhs599 1
    topEColumns topETransposeColumns tree599 allowed599 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked599 checked599
    hw (he.trans rhsChecked599) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 600. -/
noncomputable def lambdas600 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 600. -/
noncomputable def rhs600 : Nat := 0x492000ff6000012000024900000d80000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked600 : reconX topRColumns 0x47c04400a0020000000000000018006004800c00100 = rhs600 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 600. -/
theorem initialChecked600 : checkSearchInitial 8 180 12 rows600 lambdas600 0x100 0x47c04400a0020000000000000018006004800c00100 rhs600 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 600 has a listed outside support. -/
theorem complete600 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x47c04400a0020000000000000018006004800c00100)
    (hweight : bitCount 180 (outsideMask word 0x47c04400a0020000000000000018006004800c00100) ≤ 1) :
    outsideMask word 0x47c04400a0020000000000000018006004800c00100 ∈ allowed600 := by
  exact outside_mem_of_search 8 180 12 rows600 lambdas600 0x100 0x47c04400a0020000000000000018006004800c00100 rhs600 1
    topEColumns topETransposeColumns tree600 allowed600 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked600 checked600
    hw (he.trans rhsChecked600) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 601. -/
noncomputable def lambdas601 : Nat := 0x200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000180000000000000000000000000000001000000000000000000000000000000018000000000000000000000000000000440000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000600000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 601. -/
noncomputable def rhs601 : Nat := 0x9000000006c0024000000024492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked601 : reconX topRColumns 0x4800920020000000fc01c0000020000604000100000 = rhs601 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 601. -/
theorem initialChecked601 : checkSearchInitial 8 180 12 rows601 lambdas601 0x8 0x4800920020000000fc01c0000020000604000100000 rhs601 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 601 has a listed outside support. -/
theorem complete601 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x4800920020000000fc01c0000020000604000100000)
    (hweight : bitCount 180 (outsideMask word 0x4800920020000000fc01c0000020000604000100000) ≤ 1) :
    outsideMask word 0x4800920020000000fc01c0000020000604000100000 ∈ allowed601 := by
  exact outside_mem_of_search 8 180 12 rows601 lambdas601 0x8 0x4800920020000000fc01c0000020000604000100000 rhs601 1
    topEColumns topETransposeColumns tree601 allowed601 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked601 checked601
    hw (he.trans rhsChecked601) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 602. -/
noncomputable def lambdas602 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000600000011000000000000000000000000000000003800000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000010000028000000a000000000000000000000000800000000000000000000000010000000a00000a00000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 602. -/
noncomputable def rhs602 : Nat := 0x936000000000000b40000000036d8001b6c0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked602 : reconX topRColumns 0x5000000000021a04a00b408000000280000000e8000 = rhs602 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 602. -/
theorem initialChecked602 : checkSearchInitial 8 180 11 rows602 lambdas602 0x8 0x5000000000021a04a00b408000000280000000e8000 rhs602 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 602 has a listed outside support. -/
theorem complete602 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x5000000000021a04a00b408000000280000000e8000)
    (hweight : bitCount 180 (outsideMask word 0x5000000000021a04a00b408000000280000000e8000) ≤ 1) :
    outsideMask word 0x5000000000021a04a00b408000000280000000e8000 ∈ allowed602 := by
  exact outside_mem_of_search 8 180 11 rows602 lambdas602 0x8 0x5000000000021a04a00b408000000280000000e8000 rhs602 1
    topEColumns topETransposeColumns tree602 allowed602 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked602 checked602
    hw (he.trans rhsChecked602) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 603. -/
noncomputable def lambdas603 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000200000180000006000000000000000000000001000000000000000000000000018000000600000600000000000000000800000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 603. -/
noncomputable def rhs603 : Nat := 0x12240000240000fc0000000000db6000db6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked603 : reconX topRColumns 0x7000000000000240200f80008008038000000006006 = rhs603 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 603. -/
theorem initialChecked603 : checkSearchInitial 8 180 16 rows603 lambdas603 0x1 0x7000000000000240200f80008008038000000006006 rhs603 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 603 has a listed outside support. -/
theorem complete603 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7000000000000240200f80008008038000000006006)
    (hweight : bitCount 180 (outsideMask word 0x7000000000000240200f80008008038000000006006) ≤ 1) :
    outsideMask word 0x7000000000000240200f80008008038000000006006 ∈ allowed603 := by
  exact outside_mem_of_search 8 180 16 rows603 lambdas603 0x1 0x7000000000000240200f80008008038000000006006 rhs603 1
    topEColumns topETransposeColumns tree603 allowed603 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked603 checked603
    hw (he.trans rhsChecked603) hweight

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

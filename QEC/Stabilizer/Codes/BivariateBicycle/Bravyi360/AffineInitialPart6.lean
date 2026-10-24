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
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineSearchPart6

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData
open PackedDigits BB.Bravyi360 BB.Bravyi360.FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 604. -/
noncomputable def lambdas604 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 604. -/
noncomputable def rhs604 : Nat := 0x12009036d80000fc000000000003fd80000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked604 : reconX topRColumns 0x7001200200000048008fc0001000008000001000c00 = rhs604 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 604. -/
theorem initialChecked604 : checkSearchInitial 8 180 11 rows604 lambdas604 0x80 0x7001200200000048008fc0001000008000001000c00 rhs604 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 604 has a listed outside support. -/
theorem complete604 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7001200200000048008fc0001000008000001000c00)
    (hweight : bitCount 180 (outsideMask word 0x7001200200000048008fc0001000008000001000c00) ≤ 1) :
    outsideMask word 0x7001200200000048008fc0001000008000001000c00 ∈ allowed604 := by
  exact outside_mem_of_search 8 180 11 rows604 lambdas604 0x80 0x7001200200000048008fc0001000008000001000c00 rhs604 1
    topEColumns topETransposeColumns tree604 allowed604 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked604 checked604
    hw (he.trans rhsChecked604) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 605. -/
noncomputable def lambdas605 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000002000002000000000000000000000000200000040000000000000000000000000000000000030000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 605. -/
noncomputable def rhs605 : Nat := 0x12240036d80000fc0000000000dbf000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked605 : reconX topRColumns 0x7001200200000240040fc0008000008000001006000 = rhs605 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 605. -/
theorem initialChecked605 : checkSearchInitial 8 180 11 rows605 lambdas605 0x80 0x7001200200000240040fc0008000008000001006000 rhs605 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 605 has a listed outside support. -/
theorem complete605 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7001200200000240040fc0008000008000001006000)
    (hweight : bitCount 180 (outsideMask word 0x7001200200000240040fc0008000008000001006000) ≤ 1) :
    outsideMask word 0x7001200200000240040fc0008000008000001006000 ∈ allowed605 := by
  exact outside_mem_of_search 8 180 11 rows605 lambdas605 0x80 0x7001200200000240040fc0008000008000001006000 rhs605 1
    topEColumns topETransposeColumns tree605 allowed605 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked605 checked605
    hw (he.trans rhsChecked605) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 606. -/
noncomputable def lambdas606 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000300000000000008800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 606. -/
noncomputable def rhs606 : Nat := 0x1b000036d80000fc0000000036d89000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked606 : reconX topRColumns 0x7001200200001200200fc0040000008000001030000 = rhs606 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 606. -/
theorem initialChecked606 : checkSearchInitial 8 180 12 rows606 lambdas606 0x80 0x7001200200001200200fc0040000008000001030000 rhs606 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 606 has a listed outside support. -/
theorem complete606 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7001200200001200200fc0040000008000001030000)
    (hweight : bitCount 180 (outsideMask word 0x7001200200001200200fc0040000008000001030000) ≤ 1) :
    outsideMask word 0x7001200200001200200fc0040000008000001030000 ∈ allowed606 := by
  exact outside_mem_of_search 8 180 12 rows606 lambdas606 0x80 0x7001200200001200200fc0040000008000001030000 rhs606 1
    topEColumns topETransposeColumns tree606 allowed606 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked606 checked606
    hw (he.trans rhsChecked606) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 607. -/
noncomputable def lambdas607 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000010000000000000840000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 607. -/
noncomputable def rhs607 : Nat := 0x12009024900000d80000000000024d80000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked607 : reconX topRColumns 0x7002400400000048008fc0001000010000002000c00 = rhs607 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 607. -/
theorem initialChecked607 : checkSearchInitial 8 180 11 rows607 lambdas607 0x80 0x7002400400000048008fc0001000010000002000c00 rhs607 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 607 has a listed outside support. -/
theorem complete607 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7002400400000048008fc0001000010000002000c00)
    (hweight : bitCount 180 (outsideMask word 0x7002400400000048008fc0001000010000002000c00) ≤ 1) :
    outsideMask word 0x7002400400000048008fc0001000010000002000c00 ∈ allowed607 := by
  exact outside_mem_of_search 8 180 11 rows607 lambdas607 0x80 0x7002400400000048008fc0001000010000002000c00 rhs607 1
    topEColumns topETransposeColumns tree607 allowed607 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked607 checked607
    hw (he.trans rhsChecked607) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 608. -/
noncomputable def lambdas608 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000100000000000008400000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000a00000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 608. -/
noncomputable def rhs608 : Nat := 0x12240024900000d80000000000da4000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked608 : reconX topRColumns 0x7002400400000240040fc0008000010000002006000 = rhs608 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 608. -/
theorem initialChecked608 : checkSearchInitial 8 180 11 rows608 lambdas608 0x80 0x7002400400000240040fc0008000010000002006000 rhs608 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 608 has a listed outside support. -/
theorem complete608 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7002400400000240040fc0008000010000002006000)
    (hweight : bitCount 180 (outsideMask word 0x7002400400000240040fc0008000010000002006000) ≤ 1) :
    outsideMask word 0x7002400400000240040fc0008000010000002006000 ∈ allowed608 := by
  exact outside_mem_of_search 8 180 11 rows608 lambdas608 0x80 0x7002400400000240040fc0008000010000002006000 rhs608 1
    topEColumns topETransposeColumns tree608 allowed608 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked608 checked608
    hw (he.trans rhsChecked608) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 609. -/
noncomputable def lambdas609 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 609. -/
noncomputable def rhs609 : Nat := 0x12009000000000900000000000012d80000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked609 : reconX topRColumns 0x7004800800000048008fc0001000020000004000c00 = rhs609 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 609. -/
theorem initialChecked609 : checkSearchInitial 8 180 11 rows609 lambdas609 0x80 0x7004800800000048008fc0001000020000004000c00 rhs609 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 609 has a listed outside support. -/
theorem complete609 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7004800800000048008fc0001000020000004000c00)
    (hweight : bitCount 180 (outsideMask word 0x7004800800000048008fc0001000020000004000c00) ≤ 1) :
    outsideMask word 0x7004800800000048008fc0001000020000004000c00 ∈ allowed609 := by
  exact outside_mem_of_search 8 180 11 rows609 lambdas609 0x80 0x7004800800000048008fc0001000020000004000c00 rhs609 1
    topEColumns topETransposeColumns tree609 allowed609 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked609 checked609
    hw (he.trans rhsChecked609) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 610. -/
noncomputable def lambdas610 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000600000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 610. -/
noncomputable def rhs610 : Nat := 0x12240000000000900000000000d92000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked610 : reconX topRColumns 0x7004800800000240040fc0008000020000004006000 = rhs610 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 610. -/
theorem initialChecked610 : checkSearchInitial 8 180 11 rows610 lambdas610 0x80 0x7004800800000240040fc0008000020000004006000 rhs610 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 610 has a listed outside support. -/
theorem complete610 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7004800800000240040fc0008000020000004006000)
    (hweight : bitCount 180 (outsideMask word 0x7004800800000240040fc0008000020000004006000) ≤ 1) :
    outsideMask word 0x7004800800000240040fc0008000020000004006000 ∈ allowed610 := by
  exact outside_mem_of_search 8 180 11 rows610 lambdas610 0x80 0x7004800800000240040fc0008000020000004006000 rhs610 1
    topEColumns topETransposeColumns tree610 allowed610 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked610 checked610
    hw (he.trans rhsChecked610) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 611. -/
noncomputable def lambdas611 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000010000000000000840000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 611. -/
noncomputable def rhs611 : Nat := 0x12000d92900000d80000000000252000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked611 : reconX topRColumns 0x700b401400000000000fc000000019000000a000000 = rhs611 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 611. -/
theorem initialChecked611 : checkSearchInitial 8 180 11 rows611 lambdas611 0x80 0x700b401400000000000fc000000019000000a000000 rhs611 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 611 has a listed outside support. -/
theorem complete611 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x700b401400000000000fc000000019000000a000000)
    (hweight : bitCount 180 (outsideMask word 0x700b401400000000000fc000000019000000a000000) ≤ 1) :
    outsideMask word 0x700b401400000000000fc000000019000000a000000 ∈ allowed611 := by
  exact outside_mem_of_search 8 180 11 rows611 lambdas611 0x80 0x700b401400000000000fc000000019000000a000000 rhs611 1
    topEColumns topETransposeColumns tree611 allowed611 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked611 checked611
    hw (he.trans rhsChecked611) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 612. -/
noncomputable def lambdas612 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 612. -/
noncomputable def rhs612 : Nat := 0x12000db6000000900000000000264000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked612 : reconX topRColumns 0x700d801800000000000fc00000001a000000c000000 = rhs612 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 612. -/
theorem initialChecked612 : checkSearchInitial 8 180 11 rows612 lambdas612 0x80 0x700d801800000000000fc00000001a000000c000000 rhs612 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 612 has a listed outside support. -/
theorem complete612 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x700d801800000000000fc00000001a000000c000000)
    (hweight : bitCount 180 (outsideMask word 0x700d801800000000000fc00000001a000000c000000) ≤ 1) :
    outsideMask word 0x700d801800000000000fc00000001a000000c000000 ∈ allowed612 := by
  exact outside_mem_of_search 8 180 11 rows612 lambdas612 0x80 0x700d801800000000000fc00000001a000000c000000 rhs612 1
    topEColumns topETransposeColumns tree612 allowed612 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked612 checked612
    hw (he.trans rhsChecked612) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 613. -/
noncomputable def lambdas613 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 613. -/
noncomputable def rhs613 : Nat := 0x12036db6d80000fc0000000009009000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked613 : reconX topRColumns 0x7049208200000000000fc0000000c08000041000000 = rhs613 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 613. -/
theorem initialChecked613 : checkSearchInitial 8 180 11 rows613 lambdas613 0x80 0x7049208200000000000fc0000000c08000041000000 rhs613 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 613 has a listed outside support. -/
theorem complete613 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7049208200000000000fc0000000c08000041000000)
    (hweight : bitCount 180 (outsideMask word 0x7049208200000000000fc0000000c08000041000000) ≤ 1) :
    outsideMask word 0x7049208200000000000fc0000000c08000041000000 ∈ allowed613 := by
  exact outside_mem_of_search 8 180 11 rows613 lambdas613 0x80 0x7049208200000000000fc0000000c08000041000000 rhs613 1
    topEColumns topETransposeColumns tree613 allowed613 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked613 checked613
    hw (he.trans rhsChecked613) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 614. -/
noncomputable def lambdas614 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000010000000000000840000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 614. -/
noncomputable def rhs614 : Nat := 0x12036da4900000d80000000009012000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked614 : reconX topRColumns 0x704a408400000000000fc0000000c10000042000000 = rhs614 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 614. -/
theorem initialChecked614 : checkSearchInitial 8 180 11 rows614 lambdas614 0x80 0x704a408400000000000fc0000000c10000042000000 rhs614 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 614 has a listed outside support. -/
theorem complete614 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x704a408400000000000fc0000000c10000042000000)
    (hweight : bitCount 180 (outsideMask word 0x704a408400000000000fc0000000c10000042000000) ≤ 1) :
    outsideMask word 0x704a408400000000000fc0000000c10000042000000 ∈ allowed614 := by
  exact outside_mem_of_search 8 180 11 rows614 lambdas614 0x80 0x704a408400000000000fc0000000c10000042000000 rhs614 1
    topEColumns topETransposeColumns tree614 allowed614 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked614 checked614
    hw (he.trans rhsChecked614) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 615. -/
noncomputable def lambdas615 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 615. -/
noncomputable def rhs615 : Nat := 0x12036d80000000900000000009024000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked615 : reconX topRColumns 0x704c808800000000000fc0000000c20000044000000 = rhs615 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 615. -/
theorem initialChecked615 : checkSearchInitial 8 180 11 rows615 lambdas615 0x80 0x704c808800000000000fc0000000c20000044000000 rhs615 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 615 has a listed outside support. -/
theorem complete615 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x704c808800000000000fc0000000c20000044000000)
    (hweight : bitCount 180 (outsideMask word 0x704c808800000000000fc0000000c20000044000000) ≤ 1) :
    outsideMask word 0x704c808800000000000fc0000000c20000044000000 ∈ allowed615 := by
  exact outside_mem_of_search 8 180 11 rows615 lambdas615 0x80 0x704c808800000000000fc0000000c20000044000000 rhs615 1
    topEColumns topETransposeColumns tree615 allowed615 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked615 checked615
    hw (he.trans rhsChecked615) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 616. -/
noncomputable def lambdas616 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 616. -/
noncomputable def rhs616 : Nat := 0x24d80036240000d80000009000009000492000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked616 : reconX topRColumns 0x7201000200000000fc0c40180008000001001000000 = rhs616 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 616. -/
theorem initialChecked616 : checkSearchInitial 8 180 11 rows616 lambdas616 0x2 0x7201000200000000fc0c40180008000001001000000 rhs616 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 616 has a listed outside support. -/
theorem complete616 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7201000200000000fc0c40180008000001001000000)
    (hweight : bitCount 180 (outsideMask word 0x7201000200000000fc0c40180008000001001000000) ≤ 1) :
    outsideMask word 0x7201000200000000fc0c40180008000001001000000 ∈ allowed616 := by
  exact outside_mem_of_search 8 180 11 rows616 lambdas616 0x2 0x7201000200000000fc0c40180008000001001000000 rhs616 1
    topEColumns topETransposeColumns tree616 allowed616 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked616 checked616
    hw (he.trans rhsChecked616) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 617. -/
noncomputable def lambdas617 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 617. -/
noncomputable def rhs617 : Nat := 0x12db6036d80000fc0000000240009000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked617 : reconX topRColumns 0x7241240200000000000fc0000006008000201000000 = rhs617 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 617. -/
theorem initialChecked617 : checkSearchInitial 8 180 9 rows617 lambdas617 0x20 0x7241240200000000000fc0000006008000201000000 rhs617 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 617 has a listed outside support. -/
theorem complete617 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7241240200000000000fc0000006008000201000000)
    (hweight : bitCount 180 (outsideMask word 0x7241240200000000000fc0000006008000201000000) ≤ 1) :
    outsideMask word 0x7241240200000000000fc0000006008000201000000 ∈ allowed617 := by
  exact outside_mem_of_search 8 180 9 rows617 lambdas617 0x20 0x7241240200000000000fc0000006008000201000000 rhs617 1
    topEColumns topETransposeColumns tree617 allowed617 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked617 checked617
    hw (he.trans rhsChecked617) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 618. -/
noncomputable def lambdas618 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000100000000000008400000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000a00000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 618. -/
noncomputable def rhs618 : Nat := 0x12db6024900000d80000000240012000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked618 : reconX topRColumns 0x7242440400000000000fc0000006010000202000000 = rhs618 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 618. -/
theorem initialChecked618 : checkSearchInitial 8 180 10 rows618 lambdas618 0x40 0x7242440400000000000fc0000006010000202000000 rhs618 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 618 has a listed outside support. -/
theorem complete618 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7242440400000000000fc0000006010000202000000)
    (hweight : bitCount 180 (outsideMask word 0x7242440400000000000fc0000006010000202000000) ≤ 1) :
    outsideMask word 0x7242440400000000000fc0000006010000202000000 ∈ allowed618 := by
  exact outside_mem_of_search 8 180 10 rows618 lambdas618 0x40 0x7242440400000000000fc0000006010000202000000 rhs618 1
    topEColumns topETransposeColumns tree618 allowed618 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked618 checked618
    hw (he.trans rhsChecked618) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 619. -/
noncomputable def lambdas619 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000600000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 619. -/
noncomputable def rhs619 : Nat := 0x12db6000000000900000000240024000000000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked619 : reconX topRColumns 0x7244840800000000000fc0000006020000204000000 = rhs619 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 619. -/
theorem initialChecked619 : checkSearchInitial 8 180 10 rows619 lambdas619 0x40 0x7244840800000000000fc0000006020000204000000 rhs619 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 619 has a listed outside support. -/
theorem complete619 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7244840800000000000fc0000006020000204000000)
    (hweight : bitCount 180 (outsideMask word 0x7244840800000000000fc0000006020000204000000) ≤ 1) :
    outsideMask word 0x7244840800000000000fc0000006020000204000000 ∈ allowed619 := by
  exact outside_mem_of_search 8 180 10 rows619 lambdas619 0x40 0x7244840800000000000fc0000006020000204000000 rhs619 1
    topEColumns topETransposeColumns tree619 allowed619 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked619 checked619
    hw (he.trans rhsChecked619) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 620. -/
noncomputable def lambdas620 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000018000000200000600000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 620. -/
noncomputable def rhs620 : Nat := 0x36900000000000b40000012036d80000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked620 : reconX topRColumns 0x7400400000001200040b00100020028002000030006 = rhs620 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 620. -/
theorem initialChecked620 : checkSearchInitial 8 180 13 rows620 lambdas620 0x40 0x7400400000001200040b00100020028002000030006 rhs620 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 620 has a listed outside support. -/
theorem complete620 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7400400000001200040b00100020028002000030006)
    (hweight : bitCount 180 (outsideMask word 0x7400400000001200040b00100020028002000030006) ≤ 1) :
    outsideMask word 0x7400400000001200040b00100020028002000030006 ∈ allowed620 := by
  exact outside_mem_of_search 8 180 13 rows620 lambdas620 0x40 0x7400400000001200040b00100020028002000030006 rhs620 1
    topEColumns topETransposeColumns tree620 allowed620 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked620 checked620
    hw (he.trans rhsChecked620) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 621. -/
noncomputable def lambdas621 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000001000000000000084000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000003088000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000008000000000000c000000100000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 621. -/
noncomputable def rhs621 : Nat := 0x36900024900000900000012036d92000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked621 : reconX topRColumns 0x7402000400001200040b00100020000002002030006 = rhs621 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 621. -/
theorem initialChecked621 : checkSearchInitial 8 180 14 rows621 lambdas621 0x10 0x7402000400001200040b00100020000002002030006 rhs621 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 621 has a listed outside support. -/
theorem complete621 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7402000400001200040b00100020000002002030006)
    (hweight : bitCount 180 (outsideMask word 0x7402000400001200040b00100020000002002030006) ≤ 1) :
    outsideMask word 0x7402000400001200040b00100020000002002030006 ∈ allowed621 := by
  exact outside_mem_of_search 8 180 14 rows621 lambdas621 0x10 0x7402000400001200040b00100020000002002030006 rhs621 1
    topEColumns topETransposeColumns tree621 allowed621 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked621 checked621
    hw (he.trans rhsChecked621) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 622. -/
noncomputable def lambdas622 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000c0000040000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000800000820000010000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 622. -/
noncomputable def rhs622 : Nat := 0x4800006c9000009024900000b640004add8002dd80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked622 : reconX topRColumns 0x8000000090002018202000800640040000a00140070 = rhs622 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 622. -/
theorem initialChecked622 : checkSearchInitial 8 180 12 rows622 lambdas622 0x4 0x8000000090002018202000800640040000a00140070 rhs622 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 622 has a listed outside support. -/
theorem complete622 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8000000090002018202000800640040000a00140070)
    (hweight : bitCount 180 (outsideMask word 0x8000000090002018202000800640040000a00140070) ≤ 1) :
    outsideMask word 0x8000000090002018202000800640040000a00140070 ∈ allowed622 := by
  exact outside_mem_of_search 8 180 12 rows622 lambdas622 0x4 0x8000000090002018202000800640040000a00140070 rhs622 1
    topEColumns topETransposeColumns tree622 allowed622 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked622 checked622
    hw (he.trans rhsChecked622) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 623. -/
noncomputable def lambdas623 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000c000004000000000000000000000000000000040000000000000000000000000800000008000008000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 623. -/
noncomputable def rhs623 : Nat := 0x4800006c0036d8900000000092400049200003fd80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked623 : reconX topRColumns 0x8000048008012019002200800600040c000001000c0 = rhs623 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 623. -/
theorem initialChecked623 : checkSearchInitial 8 180 11 rows623 lambdas623 0x2 0x8000048008012019002200800600040c000001000c0 rhs623 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 623 has a listed outside support. -/
theorem complete623 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8000048008012019002200800600040c000001000c0)
    (hweight : bitCount 180 (outsideMask word 0x8000048008012019002200800600040c000001000c0) ≤ 1) :
    outsideMask word 0x8000048008012019002200800600040c000001000c0 ∈ allowed623 := by
  exact outside_mem_of_search 8 180 11 rows623 lambdas623 0x2 0x8000048008012019002200800600040c000001000c0 rhs623 1
    topEColumns topETransposeColumns tree623 allowed623 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked623 checked623
    hw (he.trans rhsChecked623) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 624. -/
noncomputable def lambdas624 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000c000004000000000000000000000000000000040000000000000000000000000800000008000008000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 624. -/
noncomputable def rhs624 : Nat := 0x4800006c00000090006c00009240004bf00003fd80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked624 : reconX topRColumns 0x80001200200120190022008006000406000000400c0 = rhs624 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 624. -/
theorem initialChecked624 : checkSearchInitial 8 180 11 rows624 lambdas624 0x2 0x80001200200120190022008006000406000000400c0 rhs624 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 624 has a listed outside support. -/
theorem complete624 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x80001200200120190022008006000406000000400c0)
    (hweight : bitCount 180 (outsideMask word 0x80001200200120190022008006000406000000400c0) ≤ 1) :
    outsideMask word 0x80001200200120190022008006000406000000400c0 ∈ allowed624 := by
  exact outside_mem_of_search 8 180 11 rows624 lambdas624 0x2 0x80001200200120190022008006000406000000400c0 rhs624 1
    topEColumns topETransposeColumns tree624 allowed624 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked624 checked624
    hw (he.trans rhsChecked624) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 625. -/
noncomputable def lambdas625 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000006000002000000080000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 625. -/
noncomputable def rhs625 : Nat := 0xd80000240000009024fc0000da4000d80000000d80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked625 : reconX topRColumns 0x800012019000600f000200000200040600c00080000 = rhs625 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 625. -/
theorem initialChecked625 : checkSearchInitial 8 180 15 rows625 lambdas625 0x10 0x800012019000600f000200000200040600c00080000 rhs625 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 625 has a listed outside support. -/
theorem complete625 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x800012019000600f000200000200040600c00080000)
    (hweight : bitCount 180 (outsideMask word 0x800012019000600f000200000200040600c00080000) ≤ 1) :
    outsideMask word 0x800012019000600f000200000200040600c00080000 ∈ allowed625 := by
  exact outside_mem_of_search 8 180 15 rows625 lambdas625 0x10 0x800012019000600f000200000200040600c00080000 rhs625 1
    topEColumns topETransposeColumns tree625 allowed625 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked625 checked625
    hw (he.trans rhsChecked625) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 626. -/
noncomputable def lambdas626 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000082000000000000000000000000000004020000000000000000000000000000000000000000000000000000000800000c00000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 626. -/
noncomputable def rhs626 : Nat := 0xda40000006c00002400002400249000006d2000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked626 : reconX topRColumns 0x80010000000024002c0280100198008008000028003 = rhs626 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 626. -/
theorem initialChecked626 : checkSearchInitial 8 180 12 rows626 lambdas626 0x1 0x80010000000024002c0280100198008008000028003 rhs626 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 626 has a listed outside support. -/
theorem complete626 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x80010000000024002c0280100198008008000028003)
    (hweight : bitCount 180 (outsideMask word 0x80010000000024002c0280100198008008000028003) ≤ 1) :
    outsideMask word 0x80010000000024002c0280100198008008000028003 ∈ allowed626 := by
  exact outside_mem_of_search 8 180 12 rows626 lambdas626 0x1 0x80010000000024002c0280100198008008000028003 rhs626 1
    topEColumns topETransposeColumns tree626 allowed626 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked626 checked626
    hw (he.trans rhsChecked626) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 627. -/
noncomputable def lambdas627 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000020000020e000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 627. -/
noncomputable def rhs627 : Nat := 0xda4000036d8000048000024002492d000240000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked627 : reconX topRColumns 0x8004a00a00002400400240100180020008005028000 = rhs627 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 627. -/
theorem initialChecked627 : checkSearchInitial 8 180 15 rows627 lambdas627 0x2 0x8004a00a00002400400240100180020008005028000 rhs627 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 627 has a listed outside support. -/
theorem complete627 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8004a00a00002400400240100180020008005028000)
    (hweight : bitCount 180 (outsideMask word 0x8004a00a00002400400240100180020008005028000) ≤ 1) :
    outsideMask word 0x8004a00a00002400400240100180020008005028000 ∈ allowed627 := by
  exact outside_mem_of_search 8 180 15 rows627 lambdas627 0x2 0x8004a00a00002400400240100180020008005028000 rhs627 1
    topEColumns topETransposeColumns tree627 allowed627 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked627 checked627
    hw (he.trans rhsChecked627) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 628. -/
noncomputable def lambdas628 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000100000180000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 628. -/
noncomputable def rhs628 : Nat := 0xd92000036d8000048000024000002d0006c0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked628 : reconX topRColumns 0x8004a00a00004800800240080180020008005018000 = rhs628 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 628. -/
theorem initialChecked628 : checkSearchInitial 8 180 11 rows628 lambdas628 0x2 0x8004a00a00004800800240080180020008005018000 rhs628 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 628 has a listed outside support. -/
theorem complete628 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8004a00a00004800800240080180020008005018000)
    (hweight : bitCount 180 (outsideMask word 0x8004a00a00004800800240080180020008005018000) ≤ 1) :
    outsideMask word 0x8004a00a00004800800240080180020008005018000 ∈ allowed628 := by
  exact outside_mem_of_search 8 180 11 rows628 lambdas628 0x2 0x8004a00a00004800800240080180020008005018000 rhs628 1
    topEColumns topETransposeColumns tree628 allowed628 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked628 checked628
    hw (he.trans rhsChecked628) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 629. -/
noncomputable def lambdas629 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000800000800000008000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000082000000000000000000000000000004020000000000000000000000000000020000000c000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 629. -/
noncomputable def rhs629 : Nat := 0x36d800006c0000240036d89000000000492000db6000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked629 : reconX topRColumns 0x800800004800801b00a006000a00200040c00000080 = rhs629 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 629. -/
theorem initialChecked629 : checkSearchInitial 8 180 12 rows629 lambdas629 0x2 0x800800004800801b00a006000a00200040c00000080 rhs629 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 629 has a listed outside support. -/
theorem complete629 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x800800004800801b00a006000a00200040c00000080)
    (hweight : bitCount 180 (outsideMask word 0x800800004800801b00a006000a00200040c00000080) ≤ 1) :
    outsideMask word 0x800800004800801b00a006000a00200040c00000080 ∈ allowed629 := by
  exact outside_mem_of_search 8 180 12 rows629 lambdas629 0x2 0x800800004800801b00a006000a00200040c00000080 rhs629 1
    topEColumns topETransposeColumns tree629 allowed629 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked629 checked629
    hw (he.trans rhsChecked629) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 630. -/
noncomputable def lambdas630 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000800000800000008000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000006000002000002080000000000000000040000000000000000000000000000020000000c000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 630. -/
noncomputable def rhs630 : Nat := 0x36d800006c0000240024909000240000492000dad000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked630 : reconX topRColumns 0x800800009001001b00a006000a00200040a00000040 = rhs630 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 630. -/
theorem initialChecked630 : checkSearchInitial 8 180 12 rows630 lambdas630 0x6 0x800800009001001b00a006000a00200040a00000040 rhs630 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 630 has a listed outside support. -/
theorem complete630 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x800800009001001b00a006000a00200040a00000040)
    (hweight : bitCount 180 (outsideMask word 0x800800009001001b00a006000a00200040a00000040) ≤ 1) :
    outsideMask word 0x800800009001001b00a006000a00200040a00000040 ∈ allowed630 := by
  exact outside_mem_of_search 8 180 12 rows630 lambdas630 0x6 0x800800009001001b00a006000a00200040a00000040 rhs630 1
    topEColumns topETransposeColumns tree630 allowed630 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked630 checked630
    hw (he.trans rhsChecked630) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 631. -/
noncomputable def lambdas631 : Nat := (Nat.lor 0x2000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000001800000044000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000400000400000418000400000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000001000 (Nat.shiftLeft 0x40000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 631. -/
noncomputable def rhs631 : Nat := 0x4800000000006d20006c000090090002d000036d80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked631 : reconX topRColumns 0x8104104020012002001200800000680600120040000 = rhs631 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 631. -/
theorem initialChecked631 : checkSearchInitial 8 180 18 rows631 lambdas631 0x8 0x8104104020012002001200800000680600120040000 rhs631 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 631 has a listed outside support. -/
theorem complete631 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8104104020012002001200800000680600120040000)
    (hweight : bitCount 180 (outsideMask word 0x8104104020012002001200800000680600120040000) ≤ 1) :
    outsideMask word 0x8104104020012002001200800000680600120040000 ∈ allowed631 := by
  exact outside_mem_of_search 8 180 18 rows631 lambdas631 0x8 0x8104104020012002001200800000680600120040000 rhs631 1
    topEColumns topETransposeColumns tree631 allowed631 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked631 checked631
    hw (he.trans rhsChecked631) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 632. -/
noncomputable def lambdas632 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000001000000060000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 632. -/
noncomputable def rhs632 : Nat := 0x36d80036d8003690000000900002d000009000db6000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked632 : reconX topRColumns 0x8160060008000000009006000c00800c40140040000 = rhs632 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 632. -/
theorem initialChecked632 : checkSearchInitial 8 180 12 rows632 lambdas632 0x4 0x8160060008000000009006000c00800c40140040000 rhs632 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 632 has a listed outside support. -/
theorem complete632 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8160060008000000009006000c00800c40140040000)
    (hweight : bitCount 180 (outsideMask word 0x8160060008000000009006000c00800c40140040000) ≤ 1) :
    outsideMask word 0x8160060008000000009006000c00800c40140040000 ∈ allowed632 := by
  exact outside_mem_of_search 8 180 12 rows632 lambdas632 0x4 0x8160060008000000009006000c00800c40140040000 rhs632 1
    topEColumns topETransposeColumns tree632 allowed632 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked632 checked632
    hw (he.trans rhsChecked632) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 633. -/
noncomputable def lambdas633 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000001000000060000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 633. -/
noncomputable def rhs633 : Nat := 0x36d80036d800004800006c900002d000024000db6000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked633 : reconX topRColumns 0x8160108020000000009006000c00800640140100000 = rhs633 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 633. -/
theorem initialChecked633 : checkSearchInitial 8 180 12 rows633 lambdas633 0x4 0x8160108020000000009006000c00800640140100000 rhs633 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 633 has a listed outside support. -/
theorem complete633 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8160108020000000009006000c00800640140100000)
    (hweight : bitCount 180 (outsideMask word 0x8160108020000000009006000c00800640140100000) ≤ 1) :
    outsideMask word 0x8160108020000000009006000c00800640140100000 ∈ allowed633 := by
  exact outside_mem_of_search 8 180 12 rows633 lambdas633 0x4 0x8160108020000000009006000c00800640140100000 rhs633 1
    topEColumns topETransposeColumns tree633 allowed633 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked633 checked633
    hw (he.trans rhsChecked633) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 634. -/
noncomputable def lambdas634 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000c200000000000000000000000000000208800000000000000000000000000000c20000000000000000000000000000008040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 634. -/
noncomputable def rhs634 : Nat := 0xd80d80012fc0000000000249000000024d92000252

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked634 : reconX topRColumns 0x8201200000000002bc05c0000108000009000000028 = rhs634 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 634. -/
theorem initialChecked634 : checkSearchInitial 8 180 16 rows634 lambdas634 0x10 0x8201200000000002bc05c0000108000009000000028 rhs634 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 634 has a listed outside support. -/
theorem complete634 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8201200000000002bc05c0000108000009000000028)
    (hweight : bitCount 180 (outsideMask word 0x8201200000000002bc05c0000108000009000000028) ≤ 1) :
    outsideMask word 0x8201200000000002bc05c0000108000009000000028 ∈ allowed634 := by
  exact outside_mem_of_search 8 180 16 rows634 lambdas634 0x10 0x8201200000000002bc05c0000108000009000000028 rhs634 1
    topEColumns topETransposeColumns tree634 allowed634 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked634 checked634
    hw (he.trans rhsChecked634) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 635. -/
noncomputable def lambdas635 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000c100000000000000000000000000000108800000000000000000000000000000c10000000000000000000000000000008040000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 635. -/
noncomputable def rhs635 : Nat := 0xd80d80024fc00000000002490000000004920006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked635 : reconX topRColumns 0x82012000000000047c09c0000088000009000000018 = rhs635 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 635. -/
theorem initialChecked635 : checkSearchInitial 8 180 16 rows635 lambdas635 0x10 0x82012000000000047c09c0000088000009000000018 rhs635 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 635 has a listed outside support. -/
theorem complete635 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x82012000000000047c09c0000088000009000000018)
    (hweight : bitCount 180 (outsideMask word 0x82012000000000047c09c0000088000009000000018) ≤ 1) :
    outsideMask word 0x82012000000000047c09c0000088000009000000018 ∈ allowed635 := by
  exact outside_mem_of_search 8 180 16 rows635 lambdas635 0x10 0x82012000000000047c09c0000088000009000000018 rhs635 1
    topEColumns topETransposeColumns tree635 allowed635 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked635 checked635
    hw (he.trans rhsChecked635) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 636. -/
noncomputable def lambdas636 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000c00000000000000000000000000000030880000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 636. -/
noncomputable def rhs636 : Nat := 0xd80d80036fc0000000000249000000024d92000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked636 : reconX topRColumns 0x82012000000000063c0dc0000008000009000000030 = rhs636 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 636. -/
theorem initialChecked636 : checkSearchInitial 8 180 16 rows636 lambdas636 0x8 0x82012000000000063c0dc0000008000009000000030 rhs636 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 636 has a listed outside support. -/
theorem complete636 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x82012000000000063c0dc0000008000009000000030)
    (hweight : bitCount 180 (outsideMask word 0x82012000000000063c0dc0000008000009000000030) ≤ 1) :
    outsideMask word 0x82012000000000063c0dc0000008000009000000030 ∈ allowed636 := by
  exact outside_mem_of_search 8 180 16 rows636 lambdas636 0x8 0x82012000000000063c0dc0000008000009000000030 rhs636 1
    topEColumns topETransposeColumns tree636 allowed636 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked636 checked636
    hw (he.trans rhsChecked636) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 637. -/
noncomputable def lambdas637 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000c000000000000000000000000000000220000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 637. -/
noncomputable def rhs637 : Nat := 0xd80d8003fd80000000000249000000012da4000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked637 : reconX topRColumns 0x8201200000000007380f80000040000009000000006 = rhs637 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 637. -/
theorem initialChecked637 : checkSearchInitial 8 180 12 rows637 lambdas637 0x8 0x8201200000000007380f80000040000009000000006 rhs637 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 637 has a listed outside support. -/
theorem complete637 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8201200000000007380f80000040000009000000006)
    (hweight : bitCount 180 (outsideMask word 0x8201200000000007380f80000040000009000000006) ≤ 1) :
    outsideMask word 0x8201200000000007380f80000040000009000000006 ∈ allowed637 := by
  exact outside_mem_of_search 8 180 12 rows637 lambdas637 0x8 0x8201200000000007380f80000040000009000000006 rhs637 1
    topEColumns topETransposeColumns tree637 allowed637 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked637 checked637
    hw (he.trans rhsChecked637) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 638. -/
noncomputable def lambdas638 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000c000000000000000000000000000000220000000000000000000000000000000c00000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000030000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 638. -/
noncomputable def rhs638 : Nat := 0xd80d8003f90000000000024900000001248000049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked638 : reconX topRColumns 0x8201200000000007700f00000050000009000000003 = rhs638 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 638. -/
theorem initialChecked638 : checkSearchInitial 8 180 12 rows638 lambdas638 0x10 0x8201200000000007700f00000050000009000000003 rhs638 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 638 has a listed outside support. -/
theorem complete638 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8201200000000007700f00000050000009000000003)
    (hweight : bitCount 180 (outsideMask word 0x8201200000000007700f00000050000009000000003) ≤ 1) :
    outsideMask word 0x8201200000000007700f00000050000009000000003 ∈ allowed638 := by
  exact outside_mem_of_search 8 180 12 rows638 lambdas638 0x10 0x8201200000000007700f00000050000009000000003 rhs638 1
    topEColumns topETransposeColumns tree638 allowed638 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked638 checked638
    hw (he.trans rhsChecked638) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 639. -/
noncomputable def lambdas639 : Nat := 0x20000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000c000000000000000000000000000000220000000000000000000000000000000c00000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000030000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 639. -/
noncomputable def rhs639 : Nat := 0xd80d8003f480000000000249000000012da4000489

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked639 : reconX topRColumns 0x8201200000000007a80e80000060000009000000005 = rhs639 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 639. -/
theorem initialChecked639 : checkSearchInitial 8 180 12 rows639 lambdas639 0x10 0x8201200000000007a80e80000060000009000000005 rhs639 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 639 has a listed outside support. -/
theorem complete639 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8201200000000007a80e80000060000009000000005)
    (hweight : bitCount 180 (outsideMask word 0x8201200000000007a80e80000060000009000000005) ≤ 1) :
    outsideMask word 0x8201200000000007a80e80000060000009000000005 ∈ allowed639 := by
  exact outside_mem_of_search 8 180 12 rows639 lambdas639 0x10 0x8201200000000007a80e80000060000009000000005 rhs639 1
    topEColumns topETransposeColumns tree639 allowed639 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked639 checked639
    hw (he.trans rhsChecked639) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 640. -/
noncomputable def lambdas640 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000080000080000002200000000000000000000000000000000000000000000000000000002000002010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000c200000100000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 640. -/
noncomputable def rhs640 : Nat := 0xdad480036fc000093600025b000009000000240924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked640 : reconX topRColumns 0x860040004004000000048014019802000d001000200 = rhs640 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 640. -/
theorem initialChecked640 : checkSearchInitial 8 180 13 rows640 lambdas640 0x202 0x860040004004000000048014019802000d001000200 rhs640 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 640 has a listed outside support. -/
theorem complete640 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x860040004004000000048014019802000d001000200)
    (hweight : bitCount 180 (outsideMask word 0x860040004004000000048014019802000d001000200) ≤ 1) :
    outsideMask word 0x860040004004000000048014019802000d001000200 ∈ allowed640 := by
  exact outside_mem_of_search 8 180 13 rows640 lambdas640 0x202 0x860040004004000000048014019802000d001000200 rhs640 1
    topEColumns topETransposeColumns tree640 allowed640 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked640 checked640
    hw (he.trans rhsChecked640) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 641. -/
noncomputable def lambdas641 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000410000000600008040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000040000040000002000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000002000 (Nat.shiftLeft 0x80000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 641. -/
noncomputable def rhs641 : Nat := 0xdad000000480000b40000264000000000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked641 : reconX topRColumns 0x8801800000000000240b0014019002800c000000006 = rhs641 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 641. -/
theorem initialChecked641 : checkSearchInitial 8 180 17 rows641 lambdas641 0x1000 0x8801800000000000240b0014019002800c000000006 rhs641 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 641 has a listed outside support. -/
theorem complete641 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8801800000000000240b0014019002800c000000006)
    (hweight : bitCount 180 (outsideMask word 0x8801800000000000240b0014019002800c000000006) ≤ 1) :
    outsideMask word 0x8801800000000000240b0014019002800c000000006 ∈ allowed641 := by
  exact outside_mem_of_search 8 180 17 rows641 lambdas641 0x1000 0x8801800000000000240b0014019002800c000000006 rhs641 1
    topEColumns topETransposeColumns tree641 allowed641 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked641 checked641
    hw (he.trans rhsChecked641) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 642. -/
noncomputable def lambdas642 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000082000000000001844000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000008000000300000180000104000100000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 642. -/
noncomputable def rhs642 : Nat := 0xdb600001200000000000048001b6c0024924000b64

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked642 : reconX topRColumns 0x90010048200048024004000001000000100d800400c = rhs642 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 642. -/
theorem initialChecked642 : checkSearchInitial 8 180 15 rows642 lambdas642 0x2 0x90010048200048024004000001000000100d800400c rhs642 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 642 has a listed outside support. -/
theorem complete642 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x90010048200048024004000001000000100d800400c)
    (hweight : bitCount 180 (outsideMask word 0x90010048200048024004000001000000100d800400c) ≤ 1) :
    outsideMask word 0x90010048200048024004000001000000100d800400c ∈ allowed642 := by
  exact outside_mem_of_search 8 180 15 rows642 lambdas642 0x2 0x90010048200048024004000001000000100d800400c rhs642 1
    topEColumns topETransposeColumns tree642 allowed642 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked642 checked642
    hw (he.trans rhsChecked642) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 643. -/
noncomputable def lambdas643 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000200000000000006000002000000010000000000000000000000000000000000c00000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 643. -/
noncomputable def rhs643 : Nat := 0xd9b000000d80000480000240000009024fc0000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked643 : reconX topRColumns 0xb000200200004806400880040000020008001018030 = rhs643 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 643. -/
theorem initialChecked643 : checkSearchInitial 8 180 14 rows643 lambdas643 0x10 0xb000200200004806400880040000020008001018030 rhs643 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 643 has a listed outside support. -/
theorem complete643 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xb000200200004806400880040000020008001018030)
    (hweight : bitCount 180 (outsideMask word 0xb000200200004806400880040000020008001018030) ≤ 1) :
    outsideMask word 0xb000200200004806400880040000020008001018030 ∈ allowed643 := by
  exact outside_mem_of_search 8 180 14 rows643 lambdas643 0x10 0xb000200200004806400880040000020008001018030 rhs643 1
    topEColumns topETransposeColumns tree643 allowed643 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked643 checked643
    hw (he.trans rhsChecked643) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 644. -/
noncomputable def lambdas644 : Nat := 0x20000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000200000300000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 644. -/
noncomputable def rhs644 : Nat := 0x92d00001b480000fe400048900001b000000480924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked644 : reconX topRColumns 0x10001600280080000000480140140008015003000400 = rhs644 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 644. -/
theorem initialChecked644 : checkSearchInitial 8 180 11 rows644 lambdas644 0x2 0x10001600280080000000480140140008015003000400 rhs644 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 644 has a listed outside support. -/
theorem complete644 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10001600280080000000480140140008015003000400)
    (hweight : bitCount 180 (outsideMask word 0x10001600280080000000480140140008015003000400) ≤ 1) :
    outsideMask word 0x10001600280080000000480140140008015003000400 ∈ allowed644 := by
  exact outside_mem_of_search 8 180 11 rows644 lambdas644 0x2 0x10001600280080000000480140140008015003000400 rhs644 1
    topEColumns topETransposeColumns tree644 allowed644 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked644 checked644
    hw (he.trans rhsChecked644) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 645. -/
noncomputable def lambdas645 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000608000010000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 645. -/
noncomputable def rhs645 : Nat := 0x1b48001b480000000000924000024000000900492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked645 : reconX topRColumns 0x20e006001001000000006c00c00c0000024004000800 = rhs645 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 645. -/
theorem initialChecked645 : checkSearchInitial 8 180 12 rows645 lambdas645 0x80 0x20e006001001000000006c00c00c0000024004000800 rhs645 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 645 has a listed outside support. -/
theorem complete645 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x20e006001001000000006c00c00c0000024004000800)
    (hweight : bitCount 180 (outsideMask word 0x20e006001001000000006c00c00c0000024004000800) ≤ 1) :
    outsideMask word 0x20e006001001000000006c00c00c0000024004000800 ∈ allowed645 := by
  exact outside_mem_of_search 8 180 12 rows645 lambdas645 0x80 0x20e006001001000000006c00c00c0000024004000800 rhs645 1
    topEColumns topETransposeColumns tree645 allowed645 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked645 checked645
    hw (he.trans rhsChecked645) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 646. -/
noncomputable def lambdas646 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000006000000110000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000008200000000000000000000000000000804000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000100000100000106000000000008000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 646. -/
noncomputable def rhs646 : Nat := 0x24001b480024900000b64000db6000da4000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked646 : reconX topRColumns 0x40820120090010009008006000203400000300000100 = rhs646 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 646. -/
theorem initialChecked646 : checkSearchInitial 8 180 16 rows646 lambdas646 0x2 0x40820120090010009008006000203400000300000100 rhs646 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 646 has a listed outside support. -/
theorem complete646 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x40820120090010009008006000203400000300000100)
    (hweight : bitCount 180 (outsideMask word 0x40820120090010009008006000203400000300000100) ≤ 1) :
    outsideMask word 0x40820120090010009008006000203400000300000100 ∈ allowed646 := by
  exact outside_mem_of_search 8 180 16 rows646 lambdas646 0x2 0x40820120090010009008006000203400000300000100 rhs646 1
    topEColumns topETransposeColumns tree646 allowed646 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked646 checked646
    hw (he.trans rhsChecked646) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 647. -/
noncomputable def lambdas647 : Nat := (Nat.lor 0x2000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000104000000000006000004100000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 647. -/
noncomputable def rhs647 : Nat := 0x3603600001200000000001224001b000024000000b40

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked647 : reconX topRColumns 0x41009024020004002400400000d000000880c0020008 = rhs647 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 647. -/
theorem initialChecked647 : checkSearchInitial 8 180 18 rows647 lambdas647 0x10 0x41009024020004002400400000d000000880c0020008 rhs647 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 647 has a listed outside support. -/
theorem complete647 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x41009024020004002400400000d000000880c0020008)
    (hweight : bitCount 180 (outsideMask word 0x41009024020004002400400000d000000880c0020008) ≤ 1) :
    outsideMask word 0x41009024020004002400400000d000000880c0020008 ∈ allowed647 := by
  exact outside_mem_of_search 8 180 18 rows647 lambdas647 0x10 0x41009024020004002400400000d000000880c0020008 rhs647 1
    topEColumns topETransposeColumns tree647 allowed647 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked647 checked647
    hw (he.trans rhsChecked647) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 648. -/
noncomputable def lambdas648 : Nat := 0x200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000080000080000083100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000400000000000208000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 648. -/
noncomputable def rhs648 : Nat := 0xd80000b40000000036d89036d80000db600001200003f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked648 : reconX topRColumns 0x200200001201000940140040018000001030030004001 = rhs648 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 648. -/
theorem initialChecked648 : checkSearchInitial 8 180 15 rows648 lambdas648 0x20 0x200200001201000940140040018000001030030004001 rhs648 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 648 has a listed outside support. -/
theorem complete648 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x200200001201000940140040018000001030030004001)
    (hweight : bitCount 180 (outsideMask word 0x200200001201000940140040018000001030030004001) ≤ 1) :
    outsideMask word 0x200200001201000940140040018000001030030004001 ∈ allowed648 := by
  exact outside_mem_of_search 8 180 15 rows648 lambdas648 0x20 0x200200001201000940140040018000001030030004001 rhs648 1
    topEColumns topETransposeColumns tree648 allowed648 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked648 checked648
    hw (he.trans rhsChecked648) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 649. -/
noncomputable def lambdas649 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000c00000000000022

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 649. -/
noncomputable def rhs649 : Nat := 0xd80000fc0000000db6009000000000492000252000036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked649 : reconX topRColumns 0x200200009001000fc01c0040008000001180000008000 = rhs649 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 649. -/
theorem initialChecked649 : checkSearchInitial 8 180 11 rows649 lambdas649 0x1 0x200200009001000fc01c0040008000001180000008000 rhs649 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 649 has a listed outside support. -/
theorem complete649 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x200200009001000fc01c0040008000001180000008000)
    (hweight : bitCount 180 (outsideMask word 0x200200009001000fc01c0040008000001180000008000) ≤ 1) :
    outsideMask word 0x200200009001000fc01c0040008000001180000008000 ∈ allowed649 := by
  exact outside_mem_of_search 8 180 11 rows649 lambdas649 0x1 0x200200009001000fc01c0040008000001180000008000 rhs649 1
    topEColumns topETransposeColumns tree649 allowed649 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked649 checked649
    hw (he.trans rhsChecked649) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 650. -/
noncomputable def lambdas650 : Nat := 0x310000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000030000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 650. -/
noncomputable def rhs650 : Nat := 0x492000012000276d80000fc0000000000009db6000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked650 : reconX topRColumns 0xfc01c0048008000000240040000008000200000040006 = rhs650 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 650. -/
theorem initialChecked650 : checkSearchInitial 8 180 11 rows650 lambdas650 0x488 0xfc01c0048008000000240040000008000200000040006 rhs650 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 650 has a listed outside support. -/
theorem complete650 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc01c0048008000000240040000008000200000040006)
    (hweight : bitCount 180 (outsideMask word 0xfc01c0048008000000240040000008000200000040006) ≤ 1) :
    outsideMask word 0xfc01c0048008000000240040000008000200000040006 ∈ allowed650 := by
  exact outside_mem_of_search 8 180 11 rows650 lambdas650 0x488 0xfc01c0048008000000240040000008000200000040006 rhs650 1
    topEColumns topETransposeColumns tree650 allowed650 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked650 checked650
    hw (he.trans rhsChecked650) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 651. -/
noncomputable def lambdas651 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000010000000000000840000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 651. -/
noncomputable def rhs651 : Nat := 0x4920000120004a4900000d80000000000012924000009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked651 : reconX topRColumns 0xfc01c0090010000000480080000010000400000080005 = rhs651 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 651. -/
theorem initialChecked651 : checkSearchInitial 8 180 10 rows651 lambdas651 0x80 0xfc01c0090010000000480080000010000400000080005 rhs651 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 651 has a listed outside support. -/
theorem complete651 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc01c0090010000000480080000010000400000080005)
    (hweight : bitCount 180 (outsideMask word 0xfc01c0090010000000480080000010000400000080005) ≤ 1) :
    outsideMask word 0xfc01c0090010000000480080000010000400000080005 ∈ allowed651 := by
  exact outside_mem_of_search 8 180 10 rows651 lambdas651 0x80 0xfc01c0090010000000480080000010000400000080005 rhs651 1
    topEColumns topETransposeColumns tree651 allowed651 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked651 checked651
    hw (he.trans rhsChecked651) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 652. -/
noncomputable def lambdas652 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000020000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 652. -/
noncomputable def rhs652 : Nat := 0x49200001200090000000090000000000002400000001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked652 : reconX topRColumns 0xfc01c0120020000000900100000020000800000100003 = rhs652 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 652. -/
theorem initialChecked652 : checkSearchInitial 8 180 10 rows652 lambdas652 0x80 0xfc01c0120020000000900100000020000800000100003 rhs652 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 652 has a listed outside support. -/
theorem complete652 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc01c0120020000000900100000020000800000100003)
    (hweight : bitCount 180 (outsideMask word 0xfc01c0120020000000900100000020000800000100003) ≤ 1) :
    outsideMask word 0xfc01c0120020000000900100000020000800000100003 ∈ allowed652 := by
  exact outside_mem_of_search 8 180 10 rows652 lambdas652 0x80 0xfc01c0120020000000900100000020000800000100003 rhs652 1
    topEColumns topETransposeColumns tree652 allowed652 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked652 checked652
    hw (he.trans rhsChecked652) hweight

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

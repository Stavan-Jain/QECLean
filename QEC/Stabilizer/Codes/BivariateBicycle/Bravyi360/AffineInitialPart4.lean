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
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineSearchPart4

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData
open PackedDigits BB.Bravyi360 BB.Bravyi360.FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 404. -/
noncomputable def lambdas404 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 404. -/
noncomputable def rhs404 : Nat := 0x4b6900012000000000000fd2000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked404 : reconX topRColumns 0x103d40740000000000024018000002000003a000000 = rhs404 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 404. -/
theorem initialChecked404 : checkSearchInitial 8 180 10 rows404 lambdas404 0x8 0x103d40740000000000024018000002000003a000000 rhs404 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 404 has a listed outside support. -/
theorem complete404 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x103d40740000000000024018000002000003a000000)
    (hweight : bitCount 180 (outsideMask word 0x103d40740000000000024018000002000003a000000) ≤ 1) :
    outsideMask word 0x103d40740000000000024018000002000003a000000 ∈ allowed404 := by
  exact outside_mem_of_search 8 180 10 rows404 lambdas404 0x8 0x103d40740000000000024018000002000003a000000 rhs404 1
    topEColumns topETransposeColumns tree404 allowed404 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked404 checked404
    hw (he.trans rhsChecked404) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 405. -/
noncomputable def lambdas405 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000030000000000000000000000000000000880000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 405. -/
noncomputable def rhs405 : Nat := 0x36036000276000000000009240000240492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked405 : reconX topRColumns 0x1040000040000000fc01c000000e006001200200000 = rhs405 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 405. -/
theorem initialChecked405 : checkSearchInitial 8 180 10 rows405 lambdas405 0x8 0x1040000040000000fc01c000000e006001200200000 rhs405 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 405 has a listed outside support. -/
theorem complete405 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1040000040000000fc01c000000e006001200200000)
    (hweight : bitCount 180 (outsideMask word 0x1040000040000000fc01c000000e006001200200000) ≤ 1) :
    outsideMask word 0x1040000040000000fc01c000000e006001200200000 ∈ allowed405 := by
  exact outside_mem_of_search 8 180 10 rows405 lambdas405 0x8 0x1040000040000000fc01c000000e006001200200000 rhs405 1
    topEColumns topETransposeColumns tree405 allowed405 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked405 checked405
    hw (he.trans rhsChecked405) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 406. -/
noncomputable def lambdas406 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000001000000040000060200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 406. -/
noncomputable def rhs406 : Nat := 0x24036036000db6000036d8001248000048000092d000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked406 : reconX topRColumns 0x1040000828008020000004000036006002800400940 = rhs406 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 406. -/
theorem initialChecked406 : checkSearchInitial 8 180 14 rows406 lambdas406 0x100 0x1040000828008020000004000036006002800400940 rhs406 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 406 has a listed outside support. -/
theorem complete406 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1040000828008020000004000036006002800400940)
    (hweight : bitCount 180 (outsideMask word 0x1040000828008020000004000036006002800400940) ≤ 1) :
    outsideMask word 0x1040000828008020000004000036006002800400940 ∈ allowed406 := by
  exact outside_mem_of_search 8 180 14 rows406 lambdas406 0x100 0x1040000828008020000004000036006002800400940 rhs406 1
    topEColumns topETransposeColumns tree406 allowed406 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked406 checked406
    hw (he.trans rhsChecked406) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 407. -/
noncomputable def lambdas407 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 407. -/
noncomputable def rhs407 : Nat := 0x3603600001248000048000924000003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked407 : reconX topRColumns 0x10403b80380000000000000000360000012001c0000 = rhs407 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 407. -/
theorem initialChecked407 : checkSearchInitial 8 180 9 rows407 lambdas407 0x8 0x10403b80380000000000000000360000012001c0000 rhs407 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 407 has a listed outside support. -/
theorem complete407 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10403b80380000000000000000360000012001c0000)
    (hweight : bitCount 180 (outsideMask word 0x10403b80380000000000000000360000012001c0000) ≤ 1) :
    outsideMask word 0x10403b80380000000000000000360000012001c0000 ∈ allowed407 := by
  exact outside_mem_of_search 8 180 9 rows407 lambdas407 0x8 0x10403b80380000000000000000360000012001c0000 rhs407 1
    topEColumns topETransposeColumns tree407 allowed407 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked407 checked407
    hw (he.trans rhsChecked407) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 408. -/
noncomputable def lambdas408 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 408. -/
noncomputable def rhs408 : Nat := 0x3f036d8000000024000000001b480000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked408 : reconX topRColumns 0x1048008000007e00e00240040000c08000040000000 = rhs408 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 408. -/
theorem initialChecked408 : checkSearchInitial 8 180 11 rows408 lambdas408 0x10 0x1048008000007e00e00240040000c08000040000000 rhs408 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 408 has a listed outside support. -/
theorem complete408 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1048008000007e00e00240040000c08000040000000)
    (hweight : bitCount 180 (outsideMask word 0x1048008000007e00e00240040000c08000040000000) ≤ 1) :
    outsideMask word 0x1048008000007e00e00240040000c08000040000000 ∈ allowed408 := by
  exact outside_mem_of_search 8 180 11 rows408 lambdas408 0x10 0x1048008000007e00e00240040000c08000040000000 rhs408 1
    topEColumns topETransposeColumns tree408 allowed408 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked408 checked408
    hw (he.trans rhsChecked408) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 409. -/
noncomputable def lambdas409 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 409. -/
noncomputable def rhs409 : Nat := 0x3f024900000240240000000000480000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked409 : reconX topRColumns 0x1090010000007e00e00240040000a08000080000000 = rhs409 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 409. -/
theorem initialChecked409 : checkSearchInitial 8 180 11 rows409 lambdas409 0x10 0x1090010000007e00e00240040000a08000080000000 rhs409 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 409 has a listed outside support. -/
theorem complete409 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1090010000007e00e00240040000a08000080000000)
    (hweight : bitCount 180 (outsideMask word 0x1090010000007e00e00240040000a08000080000000) ≤ 1) :
    outsideMask word 0x1090010000007e00e00240040000a08000080000000 ∈ allowed409 := by
  exact outside_mem_of_search 8 180 11 rows409 lambdas409 0x10 0x1090010000007e00e00240040000a08000080000000 rhs409 1
    topEColumns topETransposeColumns tree409 allowed409 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked409 checked409
    hw (he.trans rhsChecked409) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 410. -/
noncomputable def lambdas410 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000002000003000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000030800000400000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 410. -/
noncomputable def rhs410 : Nat := 0xb40036b52000dad0000120000096c0000240024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked410 : reconX topRColumns 0x10c00800400000000900a8028031004001600200000 = rhs410 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 410. -/
theorem initialChecked410 : checkSearchInitial 8 180 12 rows410 lambdas410 0x21 0x10c00800400000000900a8028031004001600200000 rhs410 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 410 has a listed outside support. -/
theorem complete410 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10c00800400000000900a8028031004001600200000)
    (hweight : bitCount 180 (outsideMask word 0x10c00800400000000900a8028031004001600200000) ≤ 1) :
    outsideMask word 0x10c00800400000000900a8028031004001600200000 ∈ allowed410 := by
  exact outside_mem_of_search 8 180 12 rows410 lambdas410 0x21 0x10c00800400000000900a8028031004001600200000 rhs410 1
    topEColumns topETransposeColumns tree410 allowed410 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked410 checked410
    hw (he.trans rhsChecked410) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 411. -/
noncomputable def lambdas411 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000003000001000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 411. -/
noncomputable def rhs411 : Nat := 0xb40036b5200001b0000120000096c0000000024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked411 : reconX topRColumns 0x10c02c00000000000900a8028031002001600000000 = rhs411 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 411. -/
theorem initialChecked411 : checkSearchInitial 8 180 12 rows411 lambdas411 0x20 0x10c02c00000000000900a8028031002001600000000 rhs411 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 411 has a listed outside support. -/
theorem complete411 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10c02c00000000000900a8028031002001600000000)
    (hweight : bitCount 180 (outsideMask word 0x10c02c00000000000900a8028031002001600000000) ≤ 1) :
    outsideMask word 0x10c02c00000000000900a8028031002001600000000 ∈ allowed411 := by
  exact outside_mem_of_search 8 180 12 rows411 lambdas411 0x20 0x10c02c00000000000900a8028031002001600000000 rhs411 1
    topEColumns topETransposeColumns tree411 allowed411 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked411 checked411
    hw (he.trans rhsChecked411) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 412. -/
noncomputable def lambdas412 : Nat := 0x20000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000001000000060000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000004100004000000208000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 412. -/
noncomputable def rhs412 : Nat := 0x1b00000049b000b40000024900000000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked412 : reconX topRColumns 0x1100900000000000240b00140013028004800000006 = rhs412 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 412. -/
theorem initialChecked412 : checkSearchInitial 8 180 11 rows412 lambdas412 0x100 0x1100900000000000240b00140013028004800000006 rhs412 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 412 has a listed outside support. -/
theorem complete412 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1100900000000000240b00140013028004800000006)
    (hweight : bitCount 180 (outsideMask word 0x1100900000000000240b00140013028004800000006) ≤ 1) :
    outsideMask word 0x1100900000000000240b00140013028004800000006 ∈ allowed412 := by
  exact outside_mem_of_search 8 180 11 rows412 lambdas412 0x100 0x1100900000000000240b00140013028004800000006 rhs412 1
    topEColumns topETransposeColumns tree412 allowed412 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked412 checked412
    hw (he.trans rhsChecked412) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 413. -/
noncomputable def lambdas413 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000004000008000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000008208000800000820800000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 413. -/
noncomputable def rhs413 : Nat := 0x1b0000006db000d80000024900024000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked413 : reconX topRColumns 0x1104100800000000000b4014001b030004804000000 = rhs413 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 413. -/
theorem initialChecked413 : checkSearchInitial 8 180 12 rows413 lambdas413 0x400 0x1104100800000000000b4014001b030004804000000 rhs413 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 413 has a listed outside support. -/
theorem complete413 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1104100800000000000b4014001b030004804000000)
    (hweight : bitCount 180 (outsideMask word 0x1104100800000000000b4014001b030004804000000) ≤ 1) :
    outsideMask word 0x1104100800000000000b4014001b030004804000000 ∈ allowed413 := by
  exact outside_mem_of_search 8 180 12 rows413 lambdas413 0x400 0x1104100800000000000b4014001b030004804000000 rhs413 1
    topEColumns topETransposeColumns tree413 allowed413 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked413 checked413
    hw (he.trans rhsChecked413) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 414. -/
noncomputable def lambdas414 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 414. -/
noncomputable def rhs414 : Nat := 0x3f0000000006c0240000000036480000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked414 : reconX topRColumns 0x1120020000007e00e00240040000608000100000000 = rhs414 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 414. -/
theorem initialChecked414 : checkSearchInitial 8 180 11 rows414 lambdas414 0x10 0x1120020000007e00e00240040000608000100000000 rhs414 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 414 has a listed outside support. -/
theorem complete414 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1120020000007e00e00240040000608000100000000)
    (hweight : bitCount 180 (outsideMask word 0x1120020000007e00e00240040000608000100000000) ≤ 1) :
    outsideMask word 0x1120020000007e00e00240040000608000100000000 ∈ allowed414 := by
  exact outside_mem_of_search 8 180 11 rows414 lambdas414 0x10 0x1120020000007e00e00240040000608000100000000 rhs414 1
    topEColumns topETransposeColumns tree414 allowed414 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked414 checked414
    hw (he.trans rhsChecked414) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 415. -/
noncomputable def lambdas415 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000001000000040000060200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000008000008200000080000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 415. -/
noncomputable def rhs415 : Nat := 0x24036d80000db6000036d800126c000048000092d000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked415 : reconX topRColumns 0x1200040828008020000004000030006002a00400940 = rhs415 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 415. -/
theorem initialChecked415 : checkSearchInitial 8 180 14 rows415 lambdas415 0x100 0x1200040828008020000004000030006002a00400940 rhs415 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 415 has a listed outside support. -/
theorem complete415 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200040828008020000004000030006002a00400940)
    (hweight : bitCount 180 (outsideMask word 0x1200040828008020000004000030006002a00400940) ≤ 1) :
    outsideMask word 0x1200040828008020000004000030006002a00400940 ∈ allowed415 := by
  exact outside_mem_of_search 8 180 14 rows415 lambdas415 0x100 0x1200040828008020000004000030006002a00400940 rhs415 1
    topEColumns topETransposeColumns tree415 allowed415 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked415 checked415
    hw (he.trans rhsChecked415) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 416. -/
noncomputable def lambdas416 : Nat := (Nat.lor 0x80000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000004300000000000000000000000000000300800000000000000000000000000000430000000000000000000000000000008040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x100000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 416. -/
noncomputable def rhs416 : Nat := 0x36d8001bfc0000000000009000000012012000252

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked416 : reconX topRColumns 0x12002000000000039c07c00000c8000001000000018 = rhs416 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 416. -/
theorem initialChecked416 : checkSearchInitial 8 180 17 rows416 lambdas416 0x10 0x12002000000000039c07c00000c8000001000000018 rhs416 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 416 has a listed outside support. -/
theorem complete416 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x12002000000000039c07c00000c8000001000000018)
    (hweight : bitCount 180 (outsideMask word 0x12002000000000039c07c00000c8000001000000018) ≤ 1) :
    outsideMask word 0x12002000000000039c07c00000c8000001000000018 ∈ allowed416 := by
  exact outside_mem_of_search 8 180 17 rows416 lambdas416 0x10 0x12002000000000039c07c00000c8000001000000018 rhs416 1
    topEColumns topETransposeColumns tree416 allowed416 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked416 checked416
    hw (he.trans rhsChecked416) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 417. -/
noncomputable def lambdas417 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000083000000000000000000000000000003010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000830000000000000000000000000000008040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x80000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 417. -/
noncomputable def rhs417 : Nat := 0x36d8002dfc00000000000090000000369120006d2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked417 : reconX topRColumns 0x12002000000000055c0bc0000148000001000000028 = rhs417 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 417. -/
theorem initialChecked417 : checkSearchInitial 8 180 17 rows417 lambdas417 0x20 0x12002000000000055c0bc0000148000001000000028 rhs417 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 417 has a listed outside support. -/
theorem complete417 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x12002000000000055c0bc0000148000001000000028)
    (hweight : bitCount 180 (outsideMask word 0x12002000000000055c0bc0000148000001000000028) ≤ 1) :
    outsideMask word 0x12002000000000055c0bc0000148000001000000028 ∈ allowed417 := by
  exact outside_mem_of_search 8 180 17 rows417 lambdas417 0x20 0x12002000000000055c0bc0000148000001000000028 rhs417 1
    topEColumns topETransposeColumns tree417 allowed417 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked417 checked417
    hw (he.trans rhsChecked417) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 418. -/
noncomputable def lambdas418 : Nat := (Nat.lor 0x800000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000c3000000000000000000000000000003088000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000040000001000000000000000000000002000000010000000000000000000000008000000200000000000000000000000100000000800000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 418. -/
noncomputable def rhs418 : Nat := 0x36d80036fc0000000000009000000024d92000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked418 : reconX topRColumns 0x12002000000000063c0dc0000188000001000000030 = rhs418 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 418. -/
theorem initialChecked418 : checkSearchInitial 8 180 18 rows418 lambdas418 0x20 0x12002000000000063c0dc0000188000001000000030 rhs418 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 418 has a listed outside support. -/
theorem complete418 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x12002000000000063c0dc0000188000001000000030)
    (hweight : bitCount 180 (outsideMask word 0x12002000000000063c0dc0000188000001000000030) ≤ 1) :
    outsideMask word 0x12002000000000063c0dc0000188000001000000030 ∈ allowed418 := by
  exact outside_mem_of_search 8 180 18 rows418 lambdas418 0x20 0x12002000000000063c0dc0000188000001000000030 rhs418 1
    topEColumns topETransposeColumns tree418 allowed418 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked418 checked418
    hw (he.trans rhsChecked418) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 419. -/
noncomputable def lambdas419 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000c300000000000000000000000000000220000000000000000000000000000000c300000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 419. -/
noncomputable def rhs419 : Nat := 0x36d8003fd80000000000009000000012da4000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked419 : reconX topRColumns 0x1200200000000007380f800001c0000001000000006 = rhs419 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 419. -/
theorem initialChecked419 : checkSearchInitial 8 180 14 rows419 lambdas419 0x20 0x1200200000000007380f800001c0000001000000006 rhs419 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 419 has a listed outside support. -/
theorem complete419 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000007380f800001c0000001000000006)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000007380f800001c0000001000000006) ≤ 1) :
    outsideMask word 0x1200200000000007380f800001c0000001000000006 ∈ allowed419 := by
  exact outside_mem_of_search 8 180 14 rows419 lambdas419 0x20 0x1200200000000007380f800001c0000001000000006 rhs419 1
    topEColumns topETransposeColumns tree419 allowed419 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked419 checked419
    hw (he.trans rhsChecked419) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 420. -/
noncomputable def lambdas420 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 420. -/
noncomputable def rhs420 : Nat := 0x36d8003f90000000000000900000001248000049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked420 : reconX topRColumns 0x1200200000000007700f000001d0000001000000003 = rhs420 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 420. -/
theorem initialChecked420 : checkSearchInitial 8 180 10 rows420 lambdas420 0x8 0x1200200000000007700f000001d0000001000000003 rhs420 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 420 has a listed outside support. -/
theorem complete420 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000007700f000001d0000001000000003)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000007700f000001d0000001000000003) ≤ 1) :
    outsideMask word 0x1200200000000007700f000001d0000001000000003 ∈ allowed420 := by
  exact outside_mem_of_search 8 180 10 rows420 lambdas420 0x8 0x1200200000000007700f000001d0000001000000003 rhs420 1
    topEColumns topETransposeColumns tree420 allowed420 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked420 checked420
    hw (he.trans rhsChecked420) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 421. -/
noncomputable def lambdas421 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 421. -/
noncomputable def rhs421 : Nat := 0x36d8003f480000000000009000000012da4000489

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked421 : reconX topRColumns 0x1200200000000007a80e800001e0000001000000005 = rhs421 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 421. -/
theorem initialChecked421 : checkSearchInitial 8 180 10 rows421 lambdas421 0x8 0x1200200000000007a80e800001e0000001000000005 rhs421 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 421 has a listed outside support. -/
theorem complete421 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000007a80e800001e0000001000000005)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000007a80e800001e0000001000000005) ≤ 1) :
    outsideMask word 0x1200200000000007a80e800001e0000001000000005 ∈ allowed421 := by
  exact outside_mem_of_search 8 180 10 rows421 lambdas421 0x8 0x1200200000000007a80e800001e0000001000000005 rhs421 1
    topEColumns topETransposeColumns tree421 allowed421 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked421 checked421
    hw (he.trans rhsChecked421) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 422. -/
noncomputable def lambdas422 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 422. -/
noncomputable def rhs422 : Nat := 0x36d80240fc0000000000009000000db6492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked422 : reconX topRColumns 0x1200200000000009fc11c0000208000001000000180 = rhs422 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 422. -/
theorem initialChecked422 : checkSearchInitial 8 180 11 rows422 lambdas422 0x10 0x1200200000000009fc11c0000208000001000000180 rhs422 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 422 has a listed outside support. -/
theorem complete422 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000009fc11c0000208000001000000180)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000009fc11c0000208000001000000180) ≤ 1) :
    outsideMask word 0x1200200000000009fc11c0000208000001000000180 ∈ allowed422 := by
  exact outside_mem_of_search 8 180 11 rows422 lambdas422 0x10 0x1200200000000009fc11c0000208000001000000180 rhs422 1
    topEColumns topETransposeColumns tree422 allowed422 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked422 checked422
    hw (he.trans rhsChecked422) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 423. -/
noncomputable def lambdas423 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 423. -/
noncomputable def rhs423 : Nat := 0x36d80480fc0000000000009000000924492009012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked423 : reconX topRColumns 0x1200200000000012fc21c0000408000001000000140 = rhs423 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 423. -/
theorem initialChecked423 : checkSearchInitial 8 180 11 rows423 lambdas423 0x10 0x1200200000000012fc21c0000408000001000000140 rhs423 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 423 has a listed outside support. -/
theorem complete423 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000012fc21c0000408000001000000140)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000012fc21c0000408000001000000140) ≤ 1) :
    outsideMask word 0x1200200000000012fc21c0000408000001000000140 ∈ allowed423 := by
  exact outside_mem_of_search 8 180 11 rows423 lambdas423 0x10 0x1200200000000012fc21c0000408000001000000140 rhs423 1
    topEColumns topETransposeColumns tree423 allowed423 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked423 checked423
    hw (he.trans rhsChecked423) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 424. -/
noncomputable def lambdas424 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 424. -/
noncomputable def rhs424 : Nat := 0x36d80900fc000000000000900000000049201b012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked424 : reconX topRColumns 0x1200200000000024fc41c00008080000010000000c0 = rhs424 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 424. -/
theorem initialChecked424 : checkSearchInitial 8 180 11 rows424 lambdas424 0x10 0x1200200000000024fc41c00008080000010000000c0 rhs424 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 424 has a listed outside support. -/
theorem complete424 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000024fc41c00008080000010000000c0)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000024fc41c00008080000010000000c0) ≤ 1) :
    outsideMask word 0x1200200000000024fc41c00008080000010000000c0 ∈ allowed424 := by
  exact outside_mem_of_search 8 180 11 rows424 lambdas424 0x10 0x1200200000000024fc41c00008080000010000000c0 rhs424 1
    topEColumns topETransposeColumns tree424 allowed424 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked424 checked424
    hw (he.trans rhsChecked424) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 425. -/
noncomputable def lambdas425 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 425. -/
noncomputable def rhs425 : Nat := 0x36d89000fc0000000000009000036d80492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked425 : reconX topRColumns 0x1200200000000048fc81c0001008000001000000c00 = rhs425 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 425. -/
theorem initialChecked425 : checkSearchInitial 8 180 11 rows425 lambdas425 0x10 0x1200200000000048fc81c0001008000001000000c00 rhs425 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 425 has a listed outside support. -/
theorem complete425 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000048fc81c0001008000001000000c00)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000048fc81c0001008000001000000c00) ≤ 1) :
    outsideMask word 0x1200200000000048fc81c0001008000001000000c00 ∈ allowed425 := by
  exact outside_mem_of_search 8 180 11 rows425 lambdas425 0x10 0x1200200000000048fc81c0001008000001000000c00 rhs425 1
    topEColumns topETransposeColumns tree425 allowed425 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked425 checked425
    hw (he.trans rhsChecked425) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 426. -/
noncomputable def lambdas426 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 426. -/
noncomputable def rhs426 : Nat := 0x36d92000fc0000000000009000024900492240012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked426 : reconX topRColumns 0x1200200000000090fd01c0002008000001000000a00 = rhs426 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 426. -/
theorem initialChecked426 : checkSearchInitial 8 180 11 rows426 lambdas426 0x10 0x1200200000000090fd01c0002008000001000000a00 rhs426 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 426 has a listed outside support. -/
theorem complete426 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000090fd01c0002008000001000000a00)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000090fd01c0002008000001000000a00) ≤ 1) :
    outsideMask word 0x1200200000000090fd01c0002008000001000000a00 ∈ allowed426 := by
  exact outside_mem_of_search 8 180 11 rows426 lambdas426 0x10 0x1200200000000090fd01c0002008000001000000a00 rhs426 1
    topEColumns topETransposeColumns tree426 allowed426 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked426 checked426
    hw (he.trans rhsChecked426) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 427. -/
noncomputable def lambdas427 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 427. -/
noncomputable def rhs427 : Nat := 0x36da4000fc00000000000090000000004926c0012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked427 : reconX topRColumns 0x1200200000000120fe01c0004008000001000000600 = rhs427 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 427. -/
theorem initialChecked427 : checkSearchInitial 8 180 11 rows427 lambdas427 0x10 0x1200200000000120fe01c0004008000001000000600 rhs427 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 427 has a listed outside support. -/
theorem complete427 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000120fe01c0004008000001000000600)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000120fe01c0004008000001000000600) ≤ 1) :
    outsideMask word 0x1200200000000120fe01c0004008000001000000600 ∈ allowed427 := by
  exact outside_mem_of_search 8 180 11 rows427 lambdas427 0x10 0x1200200000000120fe01c0004008000001000000600 rhs427 1
    topEColumns topETransposeColumns tree427 allowed427 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked427 checked427
    hw (he.trans rhsChecked427) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 428. -/
noncomputable def lambdas428 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000400000c0000000000000000000000003000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 428. -/
noncomputable def rhs428 : Nat := 0x36b40000fc000000000000900049200049b000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked428 : reconX topRColumns 0x12002000000006c0f001c0018008000001000003000 = rhs428 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 428. -/
theorem initialChecked428 : checkSearchInitial 8 180 16 rows428 lambdas428 0x4 0x12002000000006c0f001c0018008000001000003000 rhs428 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 428 has a listed outside support. -/
theorem complete428 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x12002000000006c0f001c0018008000001000003000)
    (hweight : bitCount 180 (outsideMask word 0x12002000000006c0f001c0018008000001000003000) ≤ 1) :
    outsideMask word 0x12002000000006c0f001c0018008000001000003000 ∈ allowed428 := by
  exact outside_mem_of_search 8 180 16 rows428 lambdas428 0x4 0x12002000000006c0f001c0018008000001000003000 rhs428 1
    topEColumns topETransposeColumns tree428 allowed428 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked428 checked428
    hw (he.trans rhsChecked428) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 429. -/
noncomputable def lambdas429 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000800000c00000000000000000000000030000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 429. -/
noncomputable def rhs429 : Nat := 0x366c0000fc0000000000009000db6000489000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked429 : reconX topRColumns 0x1200200000000b40e801c0028008000001000005000 = rhs429 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 429. -/
theorem initialChecked429 : checkSearchInitial 8 180 16 rows429 lambdas429 0x8 0x1200200000000b40e801c0028008000001000005000 rhs429 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 429 has a listed outside support. -/
theorem complete429 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000b40e801c0028008000001000005000)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000b40e801c0028008000001000005000) ≤ 1) :
    outsideMask word 0x1200200000000b40e801c0028008000001000005000 ∈ allowed429 := by
  exact outside_mem_of_search 8 180 16 rows429 lambdas429 0x8 0x1200200000000b40e801c0028008000001000005000 rhs429 1
    topEColumns topETransposeColumns tree429 allowed429 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked429 checked429
    hw (he.trans rhsChecked429) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 430. -/
noncomputable def lambdas430 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 430. -/
noncomputable def rhs430 : Nat := 0x36000000fc0000000000009000924000480000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked430 : reconX topRColumns 0x1200200000000d80e401c0030008000001000006000 = rhs430 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 430. -/
theorem initialChecked430 : checkSearchInitial 8 180 11 rows430 lambdas430 0x10 0x1200200000000d80e401c0030008000001000006000 rhs430 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 430 has a listed outside support. -/
theorem complete430 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000d80e401c0030008000001000006000)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000d80e401c0030008000001000006000) ≤ 1) :
    outsideMask word 0x1200200000000d80e401c0030008000001000006000 ∈ allowed430 := by
  exact outside_mem_of_search 8 180 11 rows430 lambdas430 0x10 0x1200200000000d80e401c0030008000001000006000 rhs430 1
    topEColumns topETransposeColumns tree430 allowed430 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked430 checked430
    hw (he.trans rhsChecked430) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 431. -/
noncomputable def lambdas431 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 431. -/
noncomputable def rhs431 : Nat := 0x36240000d80000000000009000492000936000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked431 : reconX topRColumns 0x1200200000000fc0c40180038000000001000000006 = rhs431 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 431. -/
theorem initialChecked431 : checkSearchInitial 8 180 11 rows431 lambdas431 0x2 0x1200200000000fc0c40180038000000001000000006 rhs431 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 431 has a listed outside support. -/
theorem complete431 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000000fc0c40180038000000001000000006)
    (hweight : bitCount 180 (outsideMask word 0x1200200000000fc0c40180038000000001000000006) ≤ 1) :
    outsideMask word 0x1200200000000fc0c40180038000000001000000006 ∈ allowed431 := by
  exact outside_mem_of_search 8 180 11 rows431 lambdas431 0x2 0x1200200000000fc0c40180038000000001000000006 rhs431 1
    topEColumns topETransposeColumns tree431 allowed431 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked431 checked431
    hw (he.trans rhsChecked431) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 432. -/
noncomputable def lambdas432 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000003000000000000000000000003000000088000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 432. -/
noncomputable def rhs432 : Nat := 0x3ffc0000fc0000000000009036036000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked432 : reconX topRColumns 0x1200200000001040d801c0048008000001000036000 = rhs432 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 432. -/
theorem initialChecked432 : checkSearchInitial 8 180 14 rows432 lambdas432 0x10 0x1200200000001040d801c0048008000001000036000 rhs432 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 432 has a listed outside support. -/
theorem complete432 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000001040d801c0048008000001000036000)
    (hweight : bitCount 180 (outsideMask word 0x1200200000001040d801c0048008000001000036000) ≤ 1) :
    outsideMask word 0x1200200000001040d801c0048008000001000036000 ∈ allowed432 := by
  exact outside_mem_of_search 8 180 14 rows432 lambdas432 0x10 0x1200200000001040d801c0048008000001000036000 rhs432 1
    topEColumns topETransposeColumns tree432 allowed432 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked432 checked432
    hw (he.trans rhsChecked432) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 433. -/
noncomputable def lambdas433 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000400018000000a000002000000080008200008000000020000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 433. -/
noncomputable def rhs433 : Nat := 0x24900000fc00000000000090240240006db000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked433 : reconX topRColumns 0x1200200000002080b401c009000800000100002d000 = rhs433 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 433. -/
theorem initialChecked433 : checkSearchInitial 8 180 22 rows433 lambdas433 0x2 0x1200200000002080b401c009000800000100002d000 rhs433 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 433 has a listed outside support. -/
theorem complete433 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000002080b401c009000800000100002d000)
    (hweight : bitCount 180 (outsideMask word 0x1200200000002080b401c009000800000100002d000) ≤ 1) :
    outsideMask word 0x1200200000002080b401c009000800000100002d000 ∈ allowed433 := by
  exact outside_mem_of_search 8 180 22 rows433 lambdas433 0x2 0x1200200000002080b401c009000800000100002d000 rhs433 1
    topEColumns topETransposeColumns tree433 allowed433 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked433 checked433
    hw (he.trans rhsChecked433) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 434. -/
noncomputable def lambdas434 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000c000000000000000000000000000000220000000000000000000000000000000c00000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 434. -/
noncomputable def rhs434 : Nat := 0x2dd80000fc00000000000090124800006d2000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked434 : reconX topRColumns 0x12002000000036009c01c00c0008000001000018000 = rhs434 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 434. -/
theorem initialChecked434 : checkSearchInitial 8 180 11 rows434 lambdas434 0x2 0x12002000000036009c01c00c0008000001000018000 rhs434 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 434 has a listed outside support. -/
theorem complete434 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x12002000000036009c01c00c0008000001000018000)
    (hweight : bitCount 180 (outsideMask word 0x12002000000036009c01c00c0008000001000018000) ≤ 1) :
    outsideMask word 0x12002000000036009c01c00c0008000001000018000 ∈ allowed434 := by
  exact outside_mem_of_search 8 180 11 rows434 lambdas434 0x2 0x12002000000036009c01c00c0008000001000018000 rhs434 1
    topEColumns topETransposeColumns tree434 allowed434 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked434 checked434
    hw (he.trans rhsChecked434) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 435. -/
noncomputable def lambdas435 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000018000000a000002000000080000000008000000020000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x80000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 435. -/
noncomputable def rhs435 : Nat := 0x12480000fc0000000000009000000000249000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked435 : reconX topRColumns 0x12002000000041006c01c012000800000100001b000 = rhs435 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 435. -/
theorem initialChecked435 : checkSearchInitial 8 180 20 rows435 lambdas435 0x2 0x12002000000041006c01c012000800000100001b000 rhs435 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 435 has a listed outside support. -/
theorem complete435 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x12002000000041006c01c012000800000100001b000)
    (hweight : bitCount 180 (outsideMask word 0x12002000000041006c01c012000800000100001b000) ≤ 1) :
    outsideMask word 0x12002000000041006c01c012000800000100001b000 ∈ allowed435 := by
  exact outside_mem_of_search 8 180 20 rows435 lambdas435 0x2 0x12002000000041006c01c012000800000100001b000 rhs435 1
    topEColumns topETransposeColumns tree435 allowed435 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked435 checked435
    hw (he.trans rhsChecked435) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 436. -/
noncomputable def lambdas436 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c000000000000000000000000000000220000000000000000000000000000000c00000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 436. -/
noncomputable def rhs436 : Nat := 0x1bd80000fc0000000000009036d80000252000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked436 : reconX topRColumns 0x1200200000005a005c01c0140008000001000028000 = rhs436 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 436. -/
theorem initialChecked436 : checkSearchInitial 8 180 11 rows436 lambdas436 0x2 0x1200200000005a005c01c0140008000001000028000 rhs436 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 436 has a listed outside support. -/
theorem complete436 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000005a005c01c0140008000001000028000)
    (hweight : bitCount 180 (outsideMask word 0x1200200000005a005c01c0140008000001000028000) ≤ 1) :
    outsideMask word 0x1200200000005a005c01c0140008000001000028000 ∈ allowed436 := by
  exact outside_mem_of_search 8 180 11 rows436 lambdas436 0x2 0x1200200000005a005c01c0140008000001000028000 rhs436 1
    topEColumns topETransposeColumns tree436 allowed436 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked436 checked436
    hw (he.trans rhsChecked436) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 437. -/
noncomputable def lambdas437 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000c000000000000000000000000000000220000000000000000000000000000000c00000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 437. -/
noncomputable def rhs437 : Nat := 0xd80000fc0000000000009024900000012000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked437 : reconX topRColumns 0x1200200000006c003c01c0180008000001000030000 = rhs437 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 437. -/
theorem initialChecked437 : checkSearchInitial 8 180 10 rows437 lambdas437 0x2 0x1200200000006c003c01c0180008000001000030000 rhs437 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 437 has a listed outside support. -/
theorem complete437 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000006c003c01c0180008000001000030000)
    (hweight : bitCount 180 (outsideMask word 0x1200200000006c003c01c0180008000001000030000) ≤ 1) :
    outsideMask word 0x1200200000006c003c01c0180008000001000030000 ∈ allowed437 := by
  exact outside_mem_of_search 8 180 10 rows437 lambdas437 0x2 0x1200200000006c003c01c0180008000001000030000 rhs437 1
    topEColumns topETransposeColumns tree437 allowed437 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked437 checked437
    hw (he.trans rhsChecked437) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 438. -/
noncomputable def lambdas438 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 438. -/
noncomputable def rhs438 : Nat := 0x9d80000d80000000000009012480000da4000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked438 : reconX topRColumns 0x1200200000007e003801801c0000000001000000006 = rhs438 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 438. -/
theorem initialChecked438 : checkSearchInitial 8 180 11 rows438 lambdas438 0x10 0x1200200000007e003801801c0000000001000000006 rhs438 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 438 has a listed outside support. -/
theorem complete438 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200000007e003801801c0000000001000000006)
    (hweight : bitCount 180 (outsideMask word 0x1200200000007e003801801c0000000001000000006) ≤ 1) :
    outsideMask word 0x1200200000007e003801801c0000000001000000006 ∈ allowed438 := by
  exact outside_mem_of_search 8 180 11 rows438 lambdas438 0x10 0x1200200000007e003801801c0000000001000000006 rhs438 1
    topEColumns topETransposeColumns tree438 allowed438 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked438 checked438
    hw (he.trans rhsChecked438) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 439. -/
noncomputable def lambdas439 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 439. -/
noncomputable def rhs439 : Nat := 0x36d80000fc0000036d80009000000000492009012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked439 : reconX topRColumns 0x1200200048008000fc01c0000008000001c00000040 = rhs439 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 439. -/
theorem initialChecked439 : checkSearchInitial 8 180 11 rows439 lambdas439 0x10 0x1200200048008000fc01c0000008000001c00000040 rhs439 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 439 has a listed outside support. -/
theorem complete439 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200200048008000fc01c0000008000001c00000040)
    (hweight : bitCount 180 (outsideMask word 0x1200200048008000fc01c0000008000001c00000040) ≤ 1) :
    outsideMask word 0x1200200048008000fc01c0000008000001c00000040 ∈ allowed439 := by
  exact outside_mem_of_search 8 180 11 rows439 lambdas439 0x10 0x1200200048008000fc01c0000008000001c00000040 rhs439 1
    topEColumns topETransposeColumns tree439 allowed439 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked439 checked439
    hw (he.trans rhsChecked439) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 440. -/
noncomputable def lambdas440 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 440. -/
noncomputable def rhs440 : Nat := 0x36d80000fe4900000240009000000012492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked440 : reconX topRColumns 0x1200290010000000fc01c0000008000a01000080000 = rhs440 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 440. -/
theorem initialChecked440 : checkSearchInitial 8 180 11 rows440 lambdas440 0x10 0x1200290010000000fc01c0000008000a01000080000 rhs440 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 440 has a listed outside support. -/
theorem complete440 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200290010000000fc01c0000008000a01000080000)
    (hweight : bitCount 180 (outsideMask word 0x1200290010000000fc01c0000008000a01000080000) ≤ 1) :
    outsideMask word 0x1200290010000000fc01c0000008000a01000080000 ∈ allowed440 := by
  exact outside_mem_of_search 8 180 11 rows440 lambdas440 0x10 0x1200290010000000fc01c0000008000a01000080000 rhs440 1
    topEColumns topETransposeColumns tree440 allowed440 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked440 checked440
    hw (he.trans rhsChecked440) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 441. -/
noncomputable def lambdas441 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 441. -/
noncomputable def rhs441 : Nat := 0x36d80000fc00000006c0009000000024492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked441 : reconX topRColumns 0x1200320020000000fc01c0000008000601000100000 = rhs441 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 441. -/
theorem initialChecked441 : checkSearchInitial 8 180 11 rows441 lambdas441 0x10 0x1200320020000000fc01c0000008000601000100000 rhs441 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 441 has a listed outside support. -/
theorem complete441 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200320020000000fc01c0000008000601000100000)
    (hweight : bitCount 180 (outsideMask word 0x1200320020000000fc01c0000008000601000100000) ≤ 1) :
    outsideMask word 0x1200320020000000fc01c0000008000601000100000 ∈ allowed441 := by
  exact outside_mem_of_search 8 180 11 rows441 lambdas441 0x10 0x1200320020000000fc01c0000008000601000100000 rhs441 1
    topEColumns topETransposeColumns tree441 allowed441 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked441 checked441
    hw (he.trans rhsChecked441) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 442. -/
noncomputable def lambdas442 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000003000000000000000000000000000000088000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 442. -/
noncomputable def rhs442 : Nat := 0x36d800006e4000009000009000000480492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked442 : reconX topRColumns 0x1200680080000000fc01c0000008005001000400000 = rhs442 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 442. -/
theorem initialChecked442 : checkSearchInitial 8 180 11 rows442 lambdas442 0x10 0x1200680080000000fc01c0000008005001000400000 rhs442 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 442 has a listed outside support. -/
theorem complete442 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200680080000000fc01c0000008005001000400000)
    (hweight : bitCount 180 (outsideMask word 0x1200680080000000fc01c0000008005001000400000) ≤ 1) :
    outsideMask word 0x1200680080000000fc01c0000008005001000400000 ∈ allowed442 := by
  exact outside_mem_of_search 8 180 11 rows442 lambdas442 0x10 0x1200680080000000fc01c0000008005001000400000 rhs442 1
    topEColumns topETransposeColumns tree442 allowed442 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked442 checked442
    hw (he.trans rhsChecked442) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 443. -/
noncomputable def lambdas443 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000003000000000000000000000000000000088000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 443. -/
noncomputable def rhs443 : Nat := 0x36d80000fc000001b000009000000900492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked443 : reconX topRColumns 0x1200b00100000000fc01c0000008003001000800000 = rhs443 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 443. -/
theorem initialChecked443 : checkSearchInitial 8 180 11 rows443 lambdas443 0x10 0x1200b00100000000fc01c0000008003001000800000 rhs443 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 443 has a listed outside support. -/
theorem complete443 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200b00100000000fc01c0000008003001000800000)
    (hweight : bitCount 180 (outsideMask word 0x1200b00100000000fc01c0000008003001000800000) ≤ 1) :
    outsideMask word 0x1200b00100000000fc01c0000008003001000800000 ∈ allowed443 := by
  exact outside_mem_of_search 8 180 11 rows443 lambdas443 0x10 0x1200b00100000000fc01c0000008003001000800000 rhs443 1
    topEColumns topETransposeColumns tree443 allowed443 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked443 checked443
    hw (he.trans rhsChecked443) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 444. -/
noncomputable def lambdas444 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000030000000c400000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 444. -/
noncomputable def rhs444 : Nat := 0x36d800004920000126c0009000000fe4000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked444 : reconX topRColumns 0x1200ce01e0000000000000000030000601000f00000 = rhs444 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 444. -/
theorem initialChecked444 : checkSearchInitial 8 180 10 rows444 lambdas444 0x10 0x1200ce01e0000000000000000030000601000f00000 rhs444 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 444 has a listed outside support. -/
theorem complete444 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200ce01e0000000000000000030000601000f00000)
    (hweight : bitCount 180 (outsideMask word 0x1200ce01e0000000000000000030000601000f00000) ≤ 1) :
    outsideMask word 0x1200ce01e0000000000000000030000601000f00000 ∈ allowed444 := by
  exact outside_mem_of_search 8 180 10 rows444 lambdas444 0x10 0x1200ce01e0000000000000000030000601000f00000 rhs444 1
    topEColumns topETransposeColumns tree444 allowed444 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked444 checked444
    hw (he.trans rhsChecked444) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 445. -/
noncomputable def lambdas445 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000030000000c400000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 445. -/
noncomputable def rhs445 : Nat := 0x36d800004b6900012240009000000fd2000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked445 : reconX topRColumns 0x1200d501d0000000000000000030000a01000e80000 = rhs445 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 445. -/
theorem initialChecked445 : checkSearchInitial 8 180 10 rows445 lambdas445 0x10 0x1200d501d0000000000000000030000a01000e80000 rhs445 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 445 has a listed outside support. -/
theorem complete445 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200d501d0000000000000000030000a01000e80000)
    (hweight : bitCount 180 (outsideMask word 0x1200d501d0000000000000000030000a01000e80000) ≤ 1) :
    outsideMask word 0x1200d501d0000000000000000030000a01000e80000 ∈ allowed445 := by
  exact outside_mem_of_search 8 180 10 rows445 lambdas445 0x10 0x1200d501d0000000000000000030000a01000e80000 rhs445 1
    topEColumns topETransposeColumns tree445 allowed445 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked445 checked445
    hw (he.trans rhsChecked445) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 446. -/
noncomputable def lambdas446 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000030000000c400000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 446. -/
noncomputable def rhs446 : Nat := 0x36d800004a4d80012000009000000fc9000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked446 : reconX topRColumns 0x1200d881c8000000000000000030000c01000e40000 = rhs446 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 446. -/
theorem initialChecked446 : checkSearchInitial 8 180 10 rows446 lambdas446 0x10 0x1200d881c8000000000000000030000c01000e40000 rhs446 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 446 has a listed outside support. -/
theorem complete446 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200d881c8000000000000000030000c01000e40000)
    (hweight : bitCount 180 (outsideMask word 0x1200d881c8000000000000000030000c01000e40000) ≤ 1) :
    outsideMask word 0x1200d881c8000000000000000030000c01000e40000 ∈ allowed446 := by
  exact outside_mem_of_search 8 180 10 rows446 lambdas446 0x10 0x1200d881c8000000000000000030000c01000e40000 rhs446 1
    topEColumns topETransposeColumns tree446 allowed446 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked446 checked446
    hw (he.trans rhsChecked446) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 447. -/
noncomputable def lambdas447 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 447. -/
noncomputable def rhs447 : Nat := 0x36d80000492000024d80009000000fc0000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked447 : reconX topRColumns 0x1200dc0188008000000000000030000001c00e00040 = rhs447 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 447. -/
theorem initialChecked447 : checkSearchInitial 8 180 9 rows447 lambdas447 0x8 0x1200dc0188008000000000000030000001c00e00040 rhs447 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 447 has a listed outside support. -/
theorem complete447 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200dc0188008000000000000030000001c00e00040)
    (hweight : bitCount 180 (outsideMask word 0x1200dc0188008000000000000030000001c00e00040) ≤ 1) :
    outsideMask word 0x1200dc0188008000000000000030000001c00e00040 ∈ allowed447 := by
  exact outside_mem_of_search 8 180 9 rows447 lambdas447 0x8 0x1200dc0188008000000000000030000001c00e00040 rhs447 1
    topEColumns topETransposeColumns tree447 allowed447 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked447 checked447
    hw (he.trans rhsChecked447) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 448. -/
noncomputable def lambdas448 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 448. -/
noncomputable def rhs448 : Nat := 0x36d80000012000012000009000000fc0924000009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked448 : reconX topRColumns 0x1200dc01c0000000480080000020000001000e00005 = rhs448 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 448. -/
theorem initialChecked448 : checkSearchInitial 8 180 9 rows448 lambdas448 0x8 0x1200dc01c0000000480080000020000001000e00005 rhs448 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 448 has a listed outside support. -/
theorem complete448 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200dc01c0000000480080000020000001000e00005)
    (hweight : bitCount 180 (outsideMask word 0x1200dc01c0000000480080000020000001000e00005) ≤ 1) :
    outsideMask word 0x1200dc01c0000000480080000020000001000e00005 ∈ allowed448 := by
  exact outside_mem_of_search 8 180 9 rows448 lambdas448 0x8 0x1200dc01c0000000480080000020000001000e00005 rhs448 1
    topEColumns topETransposeColumns tree448 allowed448 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked448 checked448
    hw (he.trans rhsChecked448) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 449. -/
noncomputable def lambdas449 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 449. -/
noncomputable def rhs449 : Nat := 0x36d80000d92000012000009000000fc000000001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked449 : reconX topRColumns 0x1200dc01c0000000900100000010000001000e00003 = rhs449 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 449. -/
theorem initialChecked449 : checkSearchInitial 8 180 9 rows449 lambdas449 0x8 0x1200dc01c0000000900100000010000001000e00003 rhs449 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 449 has a listed outside support. -/
theorem complete449 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1200dc01c0000000900100000010000001000e00003)
    (hweight : bitCount 180 (outsideMask word 0x1200dc01c0000000900100000010000001000e00003) ≤ 1) :
    outsideMask word 0x1200dc01c0000000900100000010000001000e00003 ∈ allowed449 := by
  exact outside_mem_of_search 8 180 9 rows449 lambdas449 0x8 0x1200dc01c0000000900100000010000001000e00003 rhs449 1
    topEColumns topETransposeColumns tree449 allowed449 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked449 checked449
    hw (he.trans rhsChecked449) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 450. -/
noncomputable def lambdas450 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000003000000000000000000000000000000088000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 450. -/
noncomputable def rhs450 : Nat := 0x36d800246c0000240000009000012000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked450 : reconX topRColumns 0x1202600400000000fc01c0000008028001002000000 = rhs450 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 450. -/
theorem initialChecked450 : checkSearchInitial 8 180 11 rows450 lambdas450 0x10 0x1202600400000000fc01c0000008028001002000000 rhs450 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 450 has a listed outside support. -/
theorem complete450 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1202600400000000fc01c0000008028001002000000)
    (hweight : bitCount 180 (outsideMask word 0x1202600400000000fc01c0000008028001002000000) ≤ 1) :
    outsideMask word 0x1202600400000000fc01c0000008028001002000000 ∈ allowed450 := by
  exact outside_mem_of_search 8 180 11 rows450 lambdas450 0x10 0x1202600400000000fc01c0000008028001002000000 rhs450 1
    topEColumns topETransposeColumns tree450 allowed450 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked450 checked450
    hw (he.trans rhsChecked450) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 451. -/
noncomputable def lambdas451 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000003000000000000000000000000000000088000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000c0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 451. -/
noncomputable def rhs451 : Nat := 0x36d80000fc00006c0000009000024000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked451 : reconX topRColumns 0x1204a00800000000fc01c0000008018001004000000 = rhs451 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 451. -/
theorem initialChecked451 : checkSearchInitial 8 180 10 rows451 lambdas451 0x10 0x1204a00800000000fc01c0000008018001004000000 rhs451 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 451 has a listed outside support. -/
theorem complete451 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1204a00800000000fc01c0000008018001004000000)
    (hweight : bitCount 180 (outsideMask word 0x1204a00800000000fc01c0000008018001004000000) ≤ 1) :
    outsideMask word 0x1204a00800000000fc01c0000008018001004000000 ∈ allowed451 := by
  exact outside_mem_of_search 8 180 10 rows451 lambdas451 0x10 0x1204a00800000000fc01c0000008018001004000000 rhs451 1
    topEColumns topETransposeColumns tree451 allowed451 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked451 checked451
    hw (he.trans rhsChecked451) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 452. -/
noncomputable def lambdas452 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 452. -/
noncomputable def rhs452 : Nat := 0x36d8001200000048000000900003f000924000009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked452 : reconX topRColumns 0x1207c00e00000000480080000020000001007000005 = rhs452 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 452. -/
theorem initialChecked452 : checkSearchInitial 8 180 10 rows452 lambdas452 0x8 0x1207c00e00000000480080000020000001007000005 rhs452 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 452 has a listed outside support. -/
theorem complete452 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1207c00e00000000480080000020000001007000005)
    (hweight : bitCount 180 (outsideMask word 0x1207c00e00000000480080000020000001007000005) ≤ 1) :
    outsideMask word 0x1207c00e00000000480080000020000001007000005 ∈ allowed452 := by
  exact outside_mem_of_search 8 180 10 rows452 lambdas452 0x8 0x1207c00e00000000480080000020000001007000005 rhs452 1
    topEColumns topETransposeColumns tree452 allowed452 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked452 checked452
    hw (he.trans rhsChecked452) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 453. -/
noncomputable def lambdas453 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 453. -/
noncomputable def rhs453 : Nat := 0x36d80012d8000048000000900003f00000000001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked453 : reconX topRColumns 0x1207c00e00000000900100000010000001007000003 = rhs453 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 453. -/
theorem initialChecked453 : checkSearchInitial 8 180 10 rows453 lambdas453 0x8 0x1207c00e00000000900100000010000001007000003 rhs453 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 453 has a listed outside support. -/
theorem complete453 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1207c00e00000000900100000010000001007000003)
    (hweight : bitCount 180 (outsideMask word 0x1207c00e00000000900100000010000001007000003) ≤ 1) :
    outsideMask word 0x1207c00e00000000900100000010000001007000003 ∈ allowed453 := by
  exact outside_mem_of_search 8 180 10 rows453 lambdas453 0x8 0x1207c00e00000000900100000010000001007000003 rhs453 1
    topEColumns topETransposeColumns tree453 allowed453 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked453 checked453
    hw (he.trans rhsChecked453) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 454. -/
noncomputable def lambdas454 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 454. -/
noncomputable def rhs454 : Nat := 0x36d80db6fc0000000000009000240000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked454 : reconX topRColumns 0x1209201000000000fc01c0000008180001008000000 = rhs454 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 454. -/
theorem initialChecked454 : checkSearchInitial 8 180 12 rows454 lambdas454 0x10 0x1209201000000000fc01c0000008180001008000000 rhs454 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 454 has a listed outside support. -/
theorem complete454 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1209201000000000fc01c0000008180001008000000)
    (hweight : bitCount 180 (outsideMask word 0x1209201000000000fc01c0000008180001008000000) ≤ 1) :
    outsideMask word 0x1209201000000000fc01c0000008180001008000000 ∈ allowed454 := by
  exact outside_mem_of_search 8 180 12 rows454 lambdas454 0x10 0x1209201000000000fc01c0000008180001008000000 rhs454 1
    topEColumns topETransposeColumns tree454 allowed454 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked454 checked454
    hw (he.trans rhsChecked454) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 455. -/
noncomputable def lambdas455 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 455. -/
noncomputable def rhs455 : Nat := 0x36d80924fc0009000000009000480000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked455 : reconX topRColumns 0x1212202000000000fc01c0000008140001010000000 = rhs455 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 455. -/
theorem initialChecked455 : checkSearchInitial 8 180 11 rows455 lambdas455 0x10 0x1212202000000000fc01c0000008140001010000000 rhs455 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 455 has a listed outside support. -/
theorem complete455 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1212202000000000fc01c0000008140001010000000)
    (hweight : bitCount 180 (outsideMask word 0x1212202000000000fc01c0000008140001010000000) ≤ 1) :
    outsideMask word 0x1212202000000000fc01c0000008140001010000000 ∈ allowed455 := by
  exact outside_mem_of_search 8 180 11 rows455 lambdas455 0x10 0x1212202000000000fc01c0000008140001010000000 rhs455 1
    topEColumns topETransposeColumns tree455 allowed455 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked455 checked455
    hw (he.trans rhsChecked455) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 456. -/
noncomputable def lambdas456 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 456. -/
noncomputable def rhs456 : Nat := 0x36d80000fc001b000000009000900000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked456 : reconX topRColumns 0x1224204000000000fc01c00000080c0001020000000 = rhs456 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 456. -/
theorem initialChecked456 : checkSearchInitial 8 180 11 rows456 lambdas456 0x10 0x1224204000000000fc01c00000080c0001020000000 rhs456 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 456 has a listed outside support. -/
theorem complete456 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1224204000000000fc01c00000080c0001020000000)
    (hweight : bitCount 180 (outsideMask word 0x1224204000000000fc01c00000080c0001020000000) ≤ 1) :
    outsideMask word 0x1224204000000000fc01c00000080c0001020000000 ∈ allowed456 := by
  exact outside_mem_of_search 8 180 11 rows456 lambdas456 0x10 0x1224204000000000fc01c00000080c0001020000000 rhs456 1
    topEColumns topETransposeColumns tree456 allowed456 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked456 checked456
    hw (he.trans rhsChecked456) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 457. -/
noncomputable def lambdas457 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 457. -/
noncomputable def rhs457 : Nat := 0x36db6d80fc0000000000009009000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked457 : reconX topRColumns 0x1248208000000000fc01c0000008c00001040000000 = rhs457 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 457. -/
theorem initialChecked457 : checkSearchInitial 8 180 12 rows457 lambdas457 0x10 0x1248208000000000fc01c0000008c00001040000000 rhs457 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 457 has a listed outside support. -/
theorem complete457 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1248208000000000fc01c0000008c00001040000000)
    (hweight : bitCount 180 (outsideMask word 0x1248208000000000fc01c0000008c00001040000000) ≤ 1) :
    outsideMask word 0x1248208000000000fc01c0000008c00001040000000 ∈ allowed457 := by
  exact outside_mem_of_search 8 180 12 rows457 lambdas457 0x10 0x1248208000000000fc01c0000008c00001040000000 rhs457 1
    topEColumns topETransposeColumns tree457 allowed457 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked457 checked457
    hw (he.trans rhsChecked457) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 458. -/
noncomputable def lambdas458 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 458. -/
noncomputable def rhs458 : Nat := 0x1bda4036fc900048000001b480009000000000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked458 : reconX topRColumns 0x128148020000000000048014001d020003401000000 = rhs458 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 458. -/
theorem initialChecked458 : checkSearchInitial 8 180 11 rows458 lambdas458 0x40 0x128148020000000000048014001d020003401000000 rhs458 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 458 has a listed outside support. -/
theorem complete458 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x128148020000000000048014001d020003401000000)
    (hweight : bitCount 180 (outsideMask word 0x128148020000000000048014001d020003401000000) ≤ 1) :
    outsideMask word 0x128148020000000000048014001d020003401000000 ∈ allowed458 := by
  exact outside_mem_of_search 8 180 11 rows458 lambdas458 0x40 0x128148020000000000048014001d020003401000000 rhs458 1
    topEColumns topETransposeColumns tree458 allowed458 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked458 checked458
    hw (he.trans rhsChecked458) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 459. -/
noncomputable def lambdas459 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 459. -/
noncomputable def rhs459 : Nat := 0x36da4900fc0240000000009012000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked459 : reconX topRColumns 0x1290210000000000fc01c0000008a00001080000000 = rhs459 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 459. -/
theorem initialChecked459 : checkSearchInitial 8 180 11 rows459 lambdas459 0x10 0x1290210000000000fc01c0000008a00001080000000 rhs459 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 459 has a listed outside support. -/
theorem complete459 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1290210000000000fc01c0000008a00001080000000)
    (hweight : bitCount 180 (outsideMask word 0x1290210000000000fc01c0000008a00001080000000) ≤ 1) :
    outsideMask word 0x1290210000000000fc01c0000008a00001080000000 ∈ allowed459 := by
  exact outside_mem_of_search 8 180 11 rows459 lambdas459 0x10 0x1290210000000000fc01c0000008a00001080000000 rhs459 1
    topEColumns topETransposeColumns tree459 allowed459 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked459 checked459
    hw (he.trans rhsChecked459) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 460. -/
noncomputable def lambdas460 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 460. -/
noncomputable def rhs460 : Nat := 0x36d80000fc06c0000000009024000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked460 : reconX topRColumns 0x1320220000000000fc01c0000008600001100000000 = rhs460 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 460. -/
theorem initialChecked460 : checkSearchInitial 8 180 11 rows460 lambdas460 0x10 0x1320220000000000fc01c0000008600001100000000 rhs460 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 460 has a listed outside support. -/
theorem complete460 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1320220000000000fc01c0000008600001100000000)
    (hweight : bitCount 180 (outsideMask word 0x1320220000000000fc01c0000008600001100000000) ≤ 1) :
    outsideMask word 0x1320220000000000fc01c0000008600001100000000 ∈ allowed460 := by
  exact outside_mem_of_search 8 180 11 rows460 lambdas460 0x10 0x1320220000000000fc01c0000008600001100000000 rhs460 1
    topEColumns topETransposeColumns tree460 allowed460 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked460 checked460
    hw (he.trans rhsChecked460) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 461. -/
noncomputable def lambdas461 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000200000008000002000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000100000002000002080000000000000008000000040000000000000000000000020400000e10000208000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 461. -/
noncomputable def rhs461 : Nat := 0x6c0036fc000049b00001b00000900000000093648001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked461 : reconX topRColumns 0x1400200000000000458058018023003001000000005 = rhs461 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 461. -/
theorem initialChecked461 : checkSearchInitial 8 180 13 rows461 lambdas461 0x82 0x1400200000000000458058018023003001000000005 rhs461 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 461 has a listed outside support. -/
theorem complete461 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1400200000000000458058018023003001000000005)
    (hweight : bitCount 180 (outsideMask word 0x1400200000000000458058018023003001000000005) ≤ 1) :
    outsideMask word 0x1400200000000000458058018023003001000000005 ∈ allowed461 := by
  exact outside_mem_of_search 8 180 13 rows461 lambdas461 0x82 0x1400200000000000458058018023003001000000005 rhs461 1
    topEColumns topETransposeColumns tree461 allowed461 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked461 checked461
    hw (he.trans rhsChecked461) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 462. -/
noncomputable def lambdas462 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000c000004000004100000000000000000010000000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 462. -/
noncomputable def rhs462 : Nat := 0x2d900000fc00006c0000012000000000924000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked462 : reconX topRColumns 0x1400400000000000d807400c0018018002000000006 = rhs462 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 462. -/
theorem initialChecked462 : checkSearchInitial 8 180 15 rows462 lambdas462 0x2 0x1400400000000000d807400c0018018002000000006 rhs462 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 462 has a listed outside support. -/
theorem complete462 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1400400000000000d807400c0018018002000000006)
    (hweight : bitCount 180 (outsideMask word 0x1400400000000000d807400c0018018002000000006) ≤ 1) :
    outsideMask word 0x1400400000000000d807400c0018018002000000006 ∈ allowed462 := by
  exact outside_mem_of_search 8 180 15 rows462 lambdas462 0x2 0x1400400000000000d807400c0018018002000000006 rhs462 1
    topEColumns topETransposeColumns tree462 allowed462 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked462 checked462
    hw (he.trans rhsChecked462) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 463. -/
noncomputable def lambdas463 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000006000004000004100000000000000000040000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000000000c0000040000041000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000008000008a00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 463. -/
noncomputable def rhs463 : Nat := 0x2d900009d800006c0000012000000036912000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked463 : reconX topRColumns 0x1400400000000001dc05000c0050018002000000030 = rhs463 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 463. -/
theorem initialChecked463 : checkSearchInitial 8 180 15 rows463 lambdas463 0x5 0x1400400000000001dc05000c0050018002000000030 rhs463 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 463 has a listed outside support. -/
theorem complete463 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1400400000000001dc05000c0050018002000000030)
    (hweight : bitCount 180 (outsideMask word 0x1400400000000001dc05000c0050018002000000030) ≤ 1) :
    outsideMask word 0x1400400000000001dc05000c0050018002000000030 ∈ allowed463 := by
  exact outside_mem_of_search 8 180 15 rows463 lambdas463 0x5 0x1400400000000001dc05000c0050018002000000030 rhs463 1
    topEColumns topETransposeColumns tree463 allowed463 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked463 checked463
    hw (he.trans rhsChecked463) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 464. -/
noncomputable def lambdas464 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000030000000c400000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 464. -/
noncomputable def rhs464 : Nat := 0x24900000d800006c0000012036d80000492000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked464 : reconX topRColumns 0x1400400000001200dc0700080010018002000030000 = rhs464 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 464. -/
theorem initialChecked464 : checkSearchInitial 8 180 11 rows464 lambdas464 0x4 0x1400400000001200dc0700080010018002000030000 rhs464 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 464 has a listed outside support. -/
theorem complete464 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1400400000001200dc0700080010018002000030000)
    (hweight : bitCount 180 (outsideMask word 0x1400400000001200dc0700080010018002000030000) ≤ 1) :
    outsideMask word 0x1400400000001200dc0700080010018002000030000 ∈ allowed464 := by
  exact outside_mem_of_search 8 180 11 rows464 lambdas464 0x4 0x1400400000001200dc0700080010018002000030000 rhs464 1
    topEColumns topETransposeColumns tree464 allowed464 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked464 checked464
    hw (he.trans rhsChecked464) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 465. -/
noncomputable def lambdas465 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000030800000400000402000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000030000000c00000400000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 465. -/
noncomputable def rhs465 : Nat := 0x3f9000006c00006c0000012024900000b6400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked465 : reconX topRColumns 0x1400400000002400080640040038018002000028005 = rhs465 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 465. -/
theorem initialChecked465 : checkSearchInitial 8 180 15 rows465 lambdas465 0x240 0x1400400000002400080640040038018002000028005 rhs465 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 465 has a listed outside support. -/
theorem complete465 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1400400000002400080640040038018002000028005)
    (hweight : bitCount 180 (outsideMask word 0x1400400000002400080640040038018002000028005) ≤ 1) :
    outsideMask word 0x1400400000002400080640040038018002000028005 ∈ allowed465 := by
  exact outside_mem_of_search 8 180 15 rows465 lambdas465 0x240 0x1400400000002400080640040038018002000028005 rhs465 1
    topEColumns topETransposeColumns tree465 allowed465 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked465 checked465
    hw (he.trans rhsChecked465) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 466. -/
noncomputable def lambdas466 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000020000000a000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000030a000000000000000000000000000008040000000000000000000000000000000000000000000000000000000c00000400000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 466. -/
noncomputable def rhs466 : Nat := 0x369000000000006c0000012012480000ff6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked466 : reconX topRColumns 0x1400400000003600440680000020018002000018006 = rhs466 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 466. -/
theorem initialChecked466 : checkSearchInitial 8 180 12 rows466 lambdas466 0x3 0x1400400000003600440680000020018002000018006 rhs466 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 466 has a listed outside support. -/
theorem complete466 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1400400000003600440680000020018002000018006)
    (hweight : bitCount 180 (outsideMask word 0x1400400000003600440680000020018002000018006) ≤ 1) :
    outsideMask word 0x1400400000003600440680000020018002000018006 ∈ allowed466 := by
  exact outside_mem_of_search 8 180 12 rows466 lambdas466 0x3 0x1400400000003600440680000020018002000018006 rhs466 1
    topEColumns topETransposeColumns tree466 allowed466 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked466 checked466
    hw (he.trans rhsChecked466) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 467. -/
noncomputable def lambdas467 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000038a00000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000020200000e00000610000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 467. -/
noncomputable def rhs467 : Nat := 0x369000002400006c0000012012480000240000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked467 : reconX topRColumns 0x14004000000036006006c0000028018002000018000 = rhs467 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 467. -/
theorem initialChecked467 : checkSearchInitial 8 180 14 rows467 lambdas467 0x8 0x14004000000036006006c0000028018002000018000 rhs467 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 467 has a listed outside support. -/
theorem complete467 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x14004000000036006006c0000028018002000018000)
    (hweight : bitCount 180 (outsideMask word 0x14004000000036006006c0000028018002000018000) ≤ 1) :
    outsideMask word 0x14004000000036006006c0000028018002000018000 ∈ allowed467 := by
  exact outside_mem_of_search 8 180 14 rows467 lambdas467 0x8 0x14004000000036006006c0000028018002000018000 rhs467 1
    topEColumns topETransposeColumns tree467 allowed467 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked467 checked467
    hw (he.trans rhsChecked467) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 468. -/
noncomputable def lambdas468 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 468. -/
noncomputable def rhs468 : Nat := 0x2d900024480000480000012000012000492000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked468 : reconX topRColumns 0x1402000400000000fc07000c0010030002002000000 = rhs468 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 468. -/
theorem initialChecked468 : checkSearchInitial 8 180 12 rows468 lambdas468 0x4 0x1402000400000000fc07000c0010030002002000000 rhs468 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 468 has a listed outside support. -/
theorem complete468 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1402000400000000fc07000c0010030002002000000)
    (hweight : bitCount 180 (outsideMask word 0x1402000400000000fc07000c0010030002002000000) ≤ 1) :
    outsideMask word 0x1402000400000000fc07000c0010030002002000000 ∈ allowed468 := by
  exact outside_mem_of_search 8 180 12 rows468 lambdas468 0x4 0x1402000400000000fc07000c0010030002002000000 rhs468 1
    topEColumns topETransposeColumns tree468 allowed468 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked468 checked468
    hw (he.trans rhsChecked468) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 469. -/
noncomputable def lambdas469 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000c0000001000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000038000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 469. -/
noncomputable def rhs469 : Nat := 0x2d90001248000048000001200001b000db6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked469 : reconX topRColumns 0x14032006000000002406800c0020000002003000006 = rhs469 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 469. -/
theorem initialChecked469 : checkSearchInitial 8 180 11 rows469 lambdas469 0x5 0x14032006000000002406800c0020000002003000006 rhs469 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 469 has a listed outside support. -/
theorem complete469 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x14032006000000002406800c0020000002003000006)
    (hweight : bitCount 180 (outsideMask word 0x14032006000000002406800c0020000002003000006) ≤ 1) :
    outsideMask word 0x14032006000000002406800c0020000002003000006 ∈ allowed469 := by
  exact outside_mem_of_search 8 180 11 rows469 lambdas469 0x5 0x14032006000000002406800c0020000002003000006 rhs469 1
    topEColumns topETransposeColumns tree469 allowed469 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked469 checked469
    hw (he.trans rhsChecked469) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 470. -/
noncomputable def lambdas470 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 470. -/
noncomputable def rhs470 : Nat := 0x2d900000d80000000000012000024000492000480

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked470 : reconX topRColumns 0x1404c00800000000fc07000c0010000002004000000 = rhs470 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 470. -/
theorem initialChecked470 : checkSearchInitial 8 180 12 rows470 lambdas470 0x4 0x1404c00800000000fc07000c0010000002004000000 rhs470 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 470 has a listed outside support. -/
theorem complete470 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1404c00800000000fc07000c0010000002004000000)
    (hweight : bitCount 180 (outsideMask word 0x1404c00800000000fc07000c0010000002004000000) ≤ 1) :
    outsideMask word 0x1404c00800000000fc07000c0010000002004000000 ∈ allowed470 := by
  exact outside_mem_of_search 8 180 12 rows470 lambdas470 0x4 0x1404c00800000000fc07000c0010000002004000000 rhs470 1
    topEColumns topETransposeColumns tree470 allowed470 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked470 checked470
    hw (he.trans rhsChecked470) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 471. -/
noncomputable def lambdas471 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 471. -/
noncomputable def rhs471 : Nat := 0x1b936036fc000048000001b240009000000000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked471 : reconX topRColumns 0x144144020000000000048014001e020003201000000 = rhs471 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 471. -/
theorem initialChecked471 : checkSearchInitial 8 180 11 rows471 lambdas471 0x40 0x144144020000000000048014001e020003201000000 rhs471 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 471 has a listed outside support. -/
theorem complete471 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x144144020000000000048014001e020003201000000)
    (hweight : bitCount 180 (outsideMask word 0x144144020000000000048014001e020003201000000) ≤ 1) :
    outsideMask word 0x144144020000000000048014001e020003201000000 ∈ allowed471 := by
  exact outside_mem_of_search 8 180 11 rows471 lambdas471 0x40 0x144144020000000000048014001e020003201000000 rhs471 1
    topEColumns topETransposeColumns tree471 allowed471 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked471 checked471
    hw (he.trans rhsChecked471) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 472. -/
noncomputable def lambdas472 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000030000000000000000000000000000000880000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 472. -/
noncomputable def rhs472 : Nat := 0xb40036fc0000fd20000120000090000000004b6900036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked472 : reconX topRColumns 0x1600200000000000f5016802800a002001000000000 = rhs472 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 472. -/
theorem initialChecked472 : checkSearchInitial 8 180 10 rows472 lambdas472 0x8 0x1600200000000000f5016802800a002001000000000 rhs472 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 472 has a listed outside support. -/
theorem complete472 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1600200000000000f5016802800a002001000000000)
    (hweight : bitCount 180 (outsideMask word 0x1600200000000000f5016802800a002001000000000) ≤ 1) :
    outsideMask word 0x1600200000000000f5016802800a002001000000000 ∈ allowed472 := by
  exact outside_mem_of_search 8 180 10 rows472 lambdas472 0x8 0x1600200000000000f5016802800a002001000000000 rhs472 1
    topEColumns topETransposeColumns tree472 allowed472 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked472 checked472
    hw (he.trans rhsChecked472) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 473. -/
noncomputable def lambdas473 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c0000001000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000040000041000000800000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000030000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 473. -/
noncomputable def rhs473 : Nat := 0xb400366c0000d9200001200000900000000091b900036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked473 : reconX topRColumns 0x1600200000000900c10128008002002001000003006 = rhs473 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 473. -/
theorem initialChecked473 : checkSearchInitial 8 180 13 rows473 lambdas473 0x100 0x1600200000000900c10128008002002001000003006 rhs473 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 473 has a listed outside support. -/
theorem complete473 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1600200000000900c10128008002002001000003006)
    (hweight : bitCount 180 (outsideMask word 0x1600200000000900c10128008002002001000003006) ≤ 1) :
    outsideMask word 0x1600200000000900c10128008002002001000003006 ∈ allowed473 := by
  exact outside_mem_of_search 8 180 13 rows473 lambdas473 0x100 0x1600200000000900c10128008002002001000003006 rhs473 1
    topEColumns topETransposeColumns tree473 allowed473 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked473 checked473
    hw (he.trans rhsChecked473) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 474. -/
noncomputable def lambdas474 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000006000004000004180000080000000000040000000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 474. -/
noncomputable def rhs474 : Nat := 0x1b480000d8000048000001b000000000492000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked474 : reconX topRColumns 0x1600600000000000fc0540140020010003000000000 = rhs474 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 474. -/
theorem initialChecked474 : checkSearchInitial 8 180 11 rows474 lambdas474 0x4 0x1600600000000000fc0540140020010003000000000 rhs474 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 474 has a listed outside support. -/
theorem complete474 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1600600000000000fc0540140020010003000000000)
    (hweight : bitCount 180 (outsideMask word 0x1600600000000000fc0540140020010003000000000) ≤ 1) :
    outsideMask word 0x1600600000000000fc0540140020010003000000000 ∈ allowed474 := by
  exact outside_mem_of_search 8 180 11 rows474 lambdas474 0x4 0x1600600000000000fc0540140020010003000000000 rhs474 1
    topEColumns topETransposeColumns tree474 allowed474 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked474 checked474
    hw (he.trans rhsChecked474) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 475. -/
noncomputable def lambdas475 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000c0000040000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e000000000000000000000000000000040000000000000000000000000000000000000000000000000000000800000a00000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 475. -/
noncomputable def rhs475 : Nat := 0x1248000048000048000001b036d8000049200092d

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked475 : reconX topRColumns 0x16006000000012004c0440100000010003000030003 = rhs475 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 475. -/
theorem initialChecked475 : checkSearchInitial 8 180 12 rows475 lambdas475 0xa 0x16006000000012004c0440100000010003000030003 rhs475 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 475 has a listed outside support. -/
theorem complete475 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x16006000000012004c0440100000010003000030003)
    (hweight : bitCount 180 (outsideMask word 0x16006000000012004c0440100000010003000030003) ≤ 1) :
    outsideMask word 0x16006000000012004c0440100000010003000030003 ∈ allowed475 := by
  exact outside_mem_of_search 8 180 12 rows475 lambdas475 0xa 0x16006000000012004c0440100000010003000030003 rhs475 1
    topEColumns topETransposeColumns tree475 allowed475 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked475 checked475
    hw (he.trans rhsChecked475) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 476. -/
noncomputable def lambdas476 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000002000000080000020000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000300000004000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 476. -/
noncomputable def rhs476 : Nat := 0x1b4800366e400048900001b000009480000000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked476 : reconX topRColumns 0x1601080280000000000480140018025003001400000 = rhs476 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 476. -/
theorem initialChecked476 : checkSearchInitial 8 180 12 rows476 lambdas476 0x2 0x1601080280000000000480140018025003001400000 rhs476 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 476 has a listed outside support. -/
theorem complete476 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1601080280000000000480140018025003001400000)
    (hweight : bitCount 180 (outsideMask word 0x1601080280000000000480140018025003001400000) ≤ 1) :
    outsideMask word 0x1601080280000000000480140018025003001400000 ∈ allowed476 := by
  exact outside_mem_of_search 8 180 12 rows476 lambdas476 0x2 0x1601080280000000000480140018025003001400000 rhs476 1
    topEColumns topETransposeColumns tree476 allowed476 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked476 checked476
    hw (he.trans rhsChecked476) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 477. -/
noncomputable def lambdas477 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000030200000e00000c10000000000000000020000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 477. -/
noncomputable def rhs477 : Nat := 0x1b480036d8000048000001b000009000db6000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked477 : reconX topRColumns 0x16014002000000002404c0140010020003001000006 = rhs477 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 477. -/
theorem initialChecked477 : checkSearchInitial 8 180 11 rows477 lambdas477 0x40 0x16014002000000002404c0140010020003001000006 rhs477 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 477 has a listed outside support. -/
theorem complete477 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x16014002000000002404c0140010020003001000006)
    (hweight : bitCount 180 (outsideMask word 0x16014002000000002404c0140010020003001000006) ≤ 1) :
    outsideMask word 0x16014002000000002404c0140010020003001000006 ∈ allowed477 := by
  exact outside_mem_of_search 8 180 11 rows477 lambdas477 0x40 0x16014002000000002404c0140010020003001000006 rhs477 1
    topEColumns topETransposeColumns tree477 allowed477 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked477 checked477
    hw (he.trans rhsChecked477) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 478. -/
noncomputable def lambdas478 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000800000c0000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e000000000000000000000000000000040000000000000000000000000000008000000000000000000000000000000a00000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 478. -/
noncomputable def rhs478 : Nat := 0x1b48003690000048000001b00000900049200092d

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked478 : reconX topRColumns 0x16014002000000006c0440140000020003001000003 = rhs478 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 478. -/
theorem initialChecked478 : checkSearchInitial 8 180 12 rows478 lambdas478 0xa 0x16014002000000006c0440140000020003001000003 rhs478 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 478 has a listed outside support. -/
theorem complete478 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x16014002000000006c0440140000020003001000003)
    (hweight : bitCount 180 (outsideMask word 0x16014002000000006c0440140000020003001000003) ≤ 1) :
    outsideMask word 0x16014002000000006c0440140000020003001000003 ∈ allowed478 := by
  exact outside_mem_of_search 8 180 12 rows478 lambdas478 0xa 0x16014002000000006c0440140000020003001000003 rhs478 1
    topEColumns topETransposeColumns tree478 allowed478 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked478 checked478
    hw (he.trans rhsChecked478) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 479. -/
noncomputable def lambdas479 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 479. -/
noncomputable def rhs479 : Nat := 0x1b480024fc000048000001b000009024900000b64

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked479 : reconX topRColumns 0x1601400200000002400080140098020003001000028 = rhs479 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 479. -/
theorem initialChecked479 : checkSearchInitial 8 180 11 rows479 lambdas479 0x40 0x1601400200000002400080140098020003001000028 rhs479 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 479 has a listed outside support. -/
theorem complete479 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1601400200000002400080140098020003001000028)
    (hweight : bitCount 180 (outsideMask word 0x1601400200000002400080140098020003001000028) ≤ 1) :
    outsideMask word 0x1601400200000002400080140098020003001000028 ∈ allowed479 := by
  exact outside_mem_of_search 8 180 11 rows479 lambdas479 0x40 0x1601400200000002400080140098020003001000028 rhs479 1
    topEColumns topETransposeColumns tree479 allowed479 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked479 checked479
    hw (he.trans rhsChecked479) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 480. -/
noncomputable def lambdas480 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 480. -/
noncomputable def rhs480 : Nat := 0x12480036fc000048000001b036d89000000000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked480 : reconX topRColumns 0x1601400200001200200480100018020003001030000 = rhs480 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 480. -/
theorem initialChecked480 : checkSearchInitial 8 180 11 rows480 lambdas480 0x40 0x1601400200001200200480100018020003001030000 rhs480 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 480 has a listed outside support. -/
theorem complete480 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1601400200001200200480100018020003001030000)
    (hweight : bitCount 180 (outsideMask word 0x1601400200001200200480100018020003001030000) ≤ 1) :
    outsideMask word 0x1601400200001200200480100018020003001030000 ∈ allowed480 := by
  exact outside_mem_of_search 8 180 11 rows480 lambdas480 0x40 0x1601400200001200200480100018020003001030000 rhs480 1
    topEColumns topETransposeColumns tree480 allowed480 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked480 checked480
    hw (he.trans rhsChecked480) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 481. -/
noncomputable def lambdas481 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 481. -/
noncomputable def rhs481 : Nat := 0x3f480036fc000048000001b0000090006c0000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked481 : reconX topRColumns 0x1601400200004800800480040018020003001018000 = rhs481 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 481. -/
theorem initialChecked481 : checkSearchInitial 8 180 11 rows481 lambdas481 0x40 0x1601400200004800800480040018020003001018000 rhs481 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 481 has a listed outside support. -/
theorem complete481 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1601400200004800800480040018020003001018000)
    (hweight : bitCount 180 (outsideMask word 0x1601400200004800800480040018020003001018000) ≤ 1) :
    outsideMask word 0x1601400200004800800480040018020003001018000 ∈ allowed481 := by
  exact outside_mem_of_search 8 180 11 rows481 lambdas481 0x40 0x1601400200004800800480040018020003001018000 rhs481 1
    topEColumns topETransposeColumns tree481 allowed481 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked481 checked481
    hw (he.trans rhsChecked481) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 482. -/
noncomputable def lambdas482 : Nat := 0x400000000000000000000000000000000000000000000000104000000000002010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c0000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 482. -/
noncomputable def rhs482 : Nat := 0x1b480d80fc000048000001b000249000000000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked482 : reconX topRColumns 0x16084012000000000004801400181a0003009000000 = rhs482 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 482. -/
theorem initialChecked482 : checkSearchInitial 8 180 11 rows482 lambdas482 0x20 0x16084012000000000004801400181a0003009000000 rhs482 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 482 has a listed outside support. -/
theorem complete482 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x16084012000000000004801400181a0003009000000)
    (hweight : bitCount 180 (outsideMask word 0x16084012000000000004801400181a0003009000000) ≤ 1) :
    outsideMask word 0x16084012000000000004801400181a0003009000000 ∈ allowed482 := by
  exact outside_mem_of_search 8 180 11 rows482 lambdas482 0x20 0x16084012000000000004801400181a0003009000000 rhs482 1
    topEColumns topETransposeColumns tree482 allowed482 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked482 checked482
    hw (he.trans rhsChecked482) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 483. -/
noncomputable def lambdas483 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000300000000000000000000000000000008800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 483. -/
noncomputable def rhs483 : Nat := 0x364a4000fc9000000000009480000000492000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked483 : reconX topRColumns 0x1680280000000000fc01c000000d000001400000000 = rhs483 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 483. -/
theorem initialChecked483 : checkSearchInitial 8 180 11 rows483 lambdas483 0x10 0x1680280000000000fc01c000000d000001400000000 rhs483 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 483 has a listed outside support. -/
theorem complete483 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1680280000000000fc01c000000d000001400000000)
    (hweight : bitCount 180 (outsideMask word 0x1680280000000000fc01c000000d000001400000000) ≤ 1) :
    outsideMask word 0x1680280000000000fc01c000000d000001400000000 ∈ allowed483 := by
  exact outside_mem_of_search 8 180 11 rows483 lambdas483 0x10 0x1680280000000000fc01c000000d000001400000000 rhs483 1
    topEColumns topETransposeColumns tree483 allowed483 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked483 checked483
    hw (he.trans rhsChecked483) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 484. -/
noncomputable def lambdas484 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000030c000000300000020000000000000000000000000000000000000000000000010000000410000200000008040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000104000002000002080000100000000800000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 484. -/
noncomputable def rhs484 : Nat := 0x364a400049b00003fd800094800006c0000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked484 : reconX topRColumns 0x1680440088008000000000000035003001800600040 = rhs484 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 484. -/
theorem initialChecked484 : checkSearchInitial 8 180 16 rows484 lambdas484 0x80 0x1680440088008000000000000035003001800600040 rhs484 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 484 has a listed outside support. -/
theorem complete484 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1680440088008000000000000035003001800600040)
    (hweight : bitCount 180 (outsideMask word 0x1680440088008000000000000035003001800600040) ≤ 1) :
    outsideMask word 0x1680440088008000000000000035003001800600040 ∈ allowed484 := by
  exact outside_mem_of_search 8 180 16 rows484 lambdas484 0x80 0x1680440088008000000000000035003001800600040 rhs484 1
    topEColumns topETransposeColumns tree484 allowed484 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked484 checked484
    hw (he.trans rhsChecked484) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 485. -/
noncomputable def lambdas485 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000280000002000002080000000000000000800000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c200000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 485. -/
noncomputable def rhs485 : Nat := 0xb40036b40000fed00002d0000090000000004a4d80024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked485 : reconX topRColumns 0x1800200000000000ea80a802800d005001000000000 = rhs485 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 485. -/
theorem initialChecked485 : checkSearchInitial 8 180 16 rows485 lambdas485 0x2 0x1800200000000000ea80a802800d005001000000000 rhs485 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 485 has a listed outside support. -/
theorem complete485 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1800200000000000ea80a802800d005001000000000)
    (hweight : bitCount 180 (outsideMask word 0x1800200000000000ea80a802800d005001000000000) ≤ 1) :
    outsideMask word 0x1800200000000000ea80a802800d005001000000000 ∈ allowed485 := by
  exact outside_mem_of_search 8 180 16 rows485 lambdas485 0x2 0x1800200000000000ea80a802800d005001000000000 rhs485 1
    topEColumns topETransposeColumns tree485 allowed485 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked485 checked485
    hw (he.trans rhsChecked485) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 486. -/
noncomputable def lambdas486 : Nat := (Nat.lor 0x2000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000002100000080000002000000000000000201000000000000000000000000000000000600000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000008000028200000800000020000000000000000040 (Nat.shiftLeft 0x8000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 486. -/
noncomputable def rhs486 : Nat := 0x1b000009000000b40000024000000036912000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked486 : reconX topRColumns 0x18008000000000014c0980140040028004000000033 = rhs486 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 486. -/
theorem initialChecked486 : checkSearchInitial 8 180 19 rows486 lambdas486 0x10 0x18008000000000014c0980140040028004000000033 rhs486 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 486 has a listed outside support. -/
theorem complete486 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x18008000000000014c0980140040028004000000033)
    (hweight : bitCount 180 (outsideMask word 0x18008000000000014c0980140040028004000000033) ≤ 1) :
    outsideMask word 0x18008000000000014c0980140040028004000000033 ∈ allowed486 := by
  exact outside_mem_of_search 8 180 19 rows486 lambdas486 0x10 0x18008000000000014c0980140040028004000000033 rhs486 1
    topEColumns topETransposeColumns tree486 allowed486 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked486 checked486
    hw (he.trans rhsChecked486) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 487. -/
noncomputable def lambdas487 : Nat := 0x2000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000100000006000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000400000400000020000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000c220000000000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 487. -/
noncomputable def rhs487 : Nat := 0x1b240000480000b40000024000db6000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked487 : reconX topRColumns 0x1800800000000240200b00148010028004000006006 = rhs487 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 487. -/
theorem initialChecked487 : checkSearchInitial 8 180 11 rows487 lambdas487 0x100 0x1800800000000240200b00148010028004000006006 rhs487 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 487 has a listed outside support. -/
theorem complete487 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1800800000000240200b00148010028004000006006)
    (hweight : bitCount 180 (outsideMask word 0x1800800000000240200b00148010028004000006006) ≤ 1) :
    outsideMask word 0x1800800000000240200b00148010028004000006006 ∈ allowed487 := by
  exact outside_mem_of_search 8 180 11 rows487 lambdas487 0x100 0x1800800000000240200b00148010028004000006006 rhs487 1
    topEColumns topETransposeColumns tree487 allowed487 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked487 checked487
    hw (he.trans rhsChecked487) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 488. -/
noncomputable def lambdas488 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000028200000800000020000000000000000080 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 488. -/
noncomputable def rhs488 : Nat := 0x12000000000000b40000024036d80000492000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked488 : reconX topRColumns 0x18008000000012004c0b80100000028004000030003 = rhs488 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 488. -/
theorem initialChecked488 : checkSearchInitial 8 180 18 rows488 lambdas488 0x1 0x18008000000012004c0b80100000028004000030003 rhs488 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 488 has a listed outside support. -/
theorem complete488 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x18008000000012004c0b80100000028004000030003)
    (hweight : bitCount 180 (outsideMask word 0x18008000000012004c0b80100000028004000030003) ≤ 1) :
    outsideMask word 0x18008000000012004c0b80100000028004000030003 ∈ allowed488 := by
  exact outside_mem_of_search 8 180 18 rows488 lambdas488 0x1 0x18008000000012004c0b80100000028004000030003 rhs488 1
    topEColumns topETransposeColumns tree488 allowed488 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked488 checked488
    hw (he.trans rhsChecked488) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 489. -/
noncomputable def lambdas489 : Nat := 0x20000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000001000000060000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000004000004000000200000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000030000008600000000000000008000000200000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 489. -/
noncomputable def rhs489 : Nat := 0x3f000000480000b40000024000000000b76000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked489 : reconX topRColumns 0x1800800000004800a40b00040010028004000018006 = rhs489 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 489. -/
theorem initialChecked489 : checkSearchInitial 8 180 11 rows489 lambdas489 0x101 0x1800800000004800a40b00040010028004000018006 rhs489 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 489 has a listed outside support. -/
theorem complete489 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1800800000004800a40b00040010028004000018006)
    (hweight : bitCount 180 (outsideMask word 0x1800800000004800a40b00040010028004000018006) ≤ 1) :
    outsideMask word 0x1800800000004800a40b00040010028004000018006 ∈ allowed489 := by
  exact outside_mem_of_search 8 180 11 rows489 lambdas489 0x101 0x1800800000004800a40b00040010028004000018006 rhs489 1
    topEColumns topETransposeColumns tree489 allowed489 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked489 checked489
    hw (he.trans rhsChecked489) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 490. -/
noncomputable def lambdas490 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000001000000060000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000004000004000000200000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000c00000800000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 490. -/
noncomputable def rhs490 : Nat := 0x36000000480000b40000024036d80000b76000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked490 : reconX topRColumns 0x1800800000005a00840b00000010028004000028006 = rhs490 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 490. -/
theorem initialChecked490 : checkSearchInitial 8 180 12 rows490 lambdas490 0x100 0x1800800000005a00840b00000010028004000028006 rhs490 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 490 has a listed outside support. -/
theorem complete490 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1800800000005a00840b00000010028004000028006)
    (hweight : bitCount 180 (outsideMask word 0x1800800000005a00840b00000010028004000028006) ≤ 1) :
    outsideMask word 0x1800800000005a00840b00000010028004000028006 ∈ allowed490 := by
  exact outside_mem_of_search 8 180 12 rows490 lambdas490 0x100 0x1800800000005a00840b00000010028004000028006 rhs490 1
    topEColumns topETransposeColumns tree490 allowed490 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked490 checked490
    hw (he.trans rhsChecked490) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 491. -/
noncomputable def lambdas491 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000038600000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000010200000e00000a20000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 491. -/
noncomputable def rhs491 : Nat := 0x360000006c0000b40000024036d800006c0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked491 : reconX topRColumns 0x1800800000005a00a00b40000018028004000028000 = rhs491 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 491. -/
theorem initialChecked491 : checkSearchInitial 8 180 14 rows491 lambdas491 0x8 0x1800800000005a00a00b40000018028004000028000 rhs491 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 491 has a listed outside support. -/
theorem complete491 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1800800000005a00a00b40000018028004000028000)
    (hweight : bitCount 180 (outsideMask word 0x1800800000005a00a00b40000018028004000028000) ≤ 1) :
    outsideMask word 0x1800800000005a00a00b40000018028004000028000 ∈ allowed491 := by
  exact outside_mem_of_search 8 180 14 rows491 lambdas491 0x8 0x1800800000005a00a00b40000018028004000028000 rhs491 1
    topEColumns topETransposeColumns tree491 allowed491 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked491 checked491
    hw (he.trans rhsChecked491) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 492. -/
noncomputable def lambdas492 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000104000002000002200000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000001000001060000020000020100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000100000004000002000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 492. -/
noncomputable def rhs492 : Nat := 0x1b000036900000b40000024000009000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked492 : reconX topRColumns 0x1801a00200000000240b00140010018004001000006 = rhs492 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 492. -/
theorem initialChecked492 : checkSearchInitial 8 180 16 rows492 lambdas492 0x500 0x1801a00200000000240b00140010018004001000006 rhs492 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 492 has a listed outside support. -/
theorem complete492 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1801a00200000000240b00140010018004001000006)
    (hweight : bitCount 180 (outsideMask word 0x1801a00200000000240b00140010018004001000006) ≤ 1) :
    outsideMask word 0x1801a00200000000240b00140010018004001000006 ∈ allowed492 := by
  exact outside_mem_of_search 8 180 16 rows492 lambdas492 0x500 0x1801a00200000000240b00140010018004001000006 rhs492 1
    topEColumns topETransposeColumns tree492 allowed492 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked492 checked492
    hw (he.trans rhsChecked492) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 493. -/
noncomputable def lambdas493 : Nat := 0x2000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000200000800000030000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000060000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000028000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 493. -/
noncomputable def rhs493 : Nat := 0x1b000024900000900000024000012000492000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked493 : reconX topRColumns 0x1802c004000000006c0b80140000000004002000003 = rhs493 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 493. -/
theorem initialChecked493 : checkSearchInitial 8 180 13 rows493 lambdas493 0x40 0x1802c004000000006c0b80140000000004002000003 rhs493 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 493 has a listed outside support. -/
theorem complete493 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1802c004000000006c0b80140000000004002000003)
    (hweight : bitCount 180 (outsideMask word 0x1802c004000000006c0b80140000000004002000003) ≤ 1) :
    outsideMask word 0x1802c004000000006c0b80140000000004002000003 ∈ allowed493 := by
  exact outside_mem_of_search 8 180 13 rows493 lambdas493 0x40 0x1802c004000000006c0b80140000000004002000003 rhs493 1
    topEColumns topETransposeColumns tree493 allowed493 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked493 checked493
    hw (he.trans rhsChecked493) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 494. -/
noncomputable def lambdas494 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000010000000400000a0000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000010000000600000200000010000002000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000008000028000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 494. -/
noncomputable def rhs494 : Nat := 0x1b00002dd80000900000024000012036036000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked494 : reconX topRColumns 0x1802c00400000001040900140050000004002000036 = rhs494 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 494. -/
theorem initialChecked494 : checkSearchInitial 8 180 11 rows494 lambdas494 0x9 0x1802c00400000001040900140050000004002000036 rhs494 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 494 has a listed outside support. -/
theorem complete494 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1802c00400000001040900140050000004002000036)
    (hweight : bitCount 180 (outsideMask word 0x1802c00400000001040900140050000004002000036) ≤ 1) :
    outsideMask word 0x1802c00400000001040900140050000004002000036 ∈ allowed494 := by
  exact outside_mem_of_search 8 180 11 rows494 lambdas494 0x9 0x1802c00400000001040900140050000004002000036 rhs494 1
    topEColumns topETransposeColumns tree494 allowed494 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked494 checked494
    hw (he.trans rhsChecked494) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 495. -/
noncomputable def lambdas495 : Nat := (Nat.lor 0x200000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000010000000400000a000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000003088000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000010000000600000200000010000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000028000000000000000000000000000000080 (Nat.shiftLeft 0x1000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 495. -/
noncomputable def rhs495 : Nat := 0x12000024d80000900000024036d92000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked495 : reconX topRColumns 0x1802c00400001200040b00100010000004002030006 = rhs495 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 495. -/
theorem initialChecked495 : checkSearchInitial 8 180 17 rows495 lambdas495 0x40 0x1802c00400001200040b00100010000004002030006 rhs495 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 495 has a listed outside support. -/
theorem complete495 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1802c00400001200040b00100010000004002030006)
    (hweight : bitCount 180 (outsideMask word 0x1802c00400001200040b00100010000004002030006) ≤ 1) :
    outsideMask word 0x1802c00400001200040b00100010000004002030006 ∈ allowed495 := by
  exact outside_mem_of_search 8 180 17 rows495 lambdas495 0x40 0x1802c00400001200040b00100010000004002030006 rhs495 1
    topEColumns topETransposeColumns tree495 allowed495 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked495 checked495
    hw (he.trans rhsChecked495) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 496. -/
noncomputable def lambdas496 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000028000000800000820000000000000000080 (Nat.shiftLeft 0x100000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 496. -/
noncomputable def rhs496 : Nat := 0x1b000000240000d80000024000024000924000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked496 : reconX topRColumns 0x1804000800000000480bc0140008030004004000005 = rhs496 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 496. -/
theorem initialChecked496 : checkSearchInitial 8 180 17 rows496 lambdas496 0x1 0x1804000800000000480bc0140008030004004000005 rhs496 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 496 has a listed outside support. -/
theorem complete496 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800000000480bc0140008030004004000005)
    (hweight : bitCount 180 (outsideMask word 0x1804000800000000480bc0140008030004004000005) ≤ 1) :
    outsideMask word 0x1804000800000000480bc0140008030004004000005 ∈ allowed496 := by
  exact outside_mem_of_search 8 180 17 rows496 lambdas496 0x1 0x1804000800000000480bc0140008030004004000005 rhs496 1
    topEColumns topETransposeColumns tree496 allowed496 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked496 checked496
    hw (he.trans rhsChecked496) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 497. -/
noncomputable def lambdas497 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000028000000800000820000000000000000080 (Nat.shiftLeft 0x100000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 497. -/
noncomputable def rhs497 : Nat := 0x1b000000000000d80000024000024000492000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked497 : reconX topRColumns 0x18040008000000006c0b80140000030004004000003 = rhs497 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 497. -/
theorem initialChecked497 : checkSearchInitial 8 180 17 rows497 lambdas497 0x1 0x18040008000000006c0b80140000030004004000003 rhs497 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 497 has a listed outside support. -/
theorem complete497 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x18040008000000006c0b80140000030004004000003)
    (hweight : bitCount 180 (outsideMask word 0x18040008000000006c0b80140000030004004000003) ≤ 1) :
    outsideMask word 0x18040008000000006c0b80140000030004004000003 ∈ allowed497 := by
  exact outside_mem_of_search 8 180 17 rows497 lambdas497 0x1 0x18040008000000006c0b80140000030004004000003 rhs497 1
    topEColumns topETransposeColumns tree497 allowed497 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked497 checked497
    hw (he.trans rhsChecked497) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 498. -/
noncomputable def lambdas498 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000400010400000020000804000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000010000000400000800000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 498. -/
noncomputable def rhs498 : Nat := 0x1b000000fc0000d80000024000024000000000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked498 : reconX topRColumns 0x1804000800000000900a40140038030004004000003 = rhs498 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 498. -/
theorem initialChecked498 : checkSearchInitial 8 180 12 rows498 lambdas498 0x400 0x1804000800000000900a40140038030004004000003 rhs498 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 498 has a listed outside support. -/
theorem complete498 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800000000900a40140038030004004000003)
    (hweight : bitCount 180 (outsideMask word 0x1804000800000000900a40140038030004004000003) ≤ 1) :
    outsideMask word 0x1804000800000000900a40140038030004004000003 ∈ allowed498 := by
  exact outside_mem_of_search 8 180 12 rows498 lambdas498 0x400 0x1804000800000000900a40140038030004004000003 rhs498 1
    topEColumns topETransposeColumns tree498 allowed498 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked498 checked498
    hw (he.trans rhsChecked498) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 499. -/
noncomputable def lambdas499 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000400010400000020000804000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000010000000400000800000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 499. -/
noncomputable def rhs499 : Nat := 0x1b000009480000d80000024000024036036000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked499 : reconX topRColumns 0x1804000800000001040900140050030004004000036 = rhs499 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 499. -/
theorem initialChecked499 : checkSearchInitial 8 180 13 rows499 lambdas499 0x400 0x1804000800000001040900140050030004004000036 rhs499 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 499 has a listed outside support. -/
theorem complete499 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800000001040900140050030004004000036)
    (hweight : bitCount 180 (outsideMask word 0x1804000800000001040900140050030004004000036) ≤ 1) :
    outsideMask word 0x1804000800000001040900140050030004004000036 ∈ allowed499 := by
  exact outside_mem_of_search 8 180 13 rows499 lambdas499 0x400 0x1804000800000001040900140050030004004000036 rhs499 1
    topEColumns topETransposeColumns tree499 allowed499 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked499 checked499
    hw (he.trans rhsChecked499) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 500. -/
noncomputable def lambdas500 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000004000008000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000200000a00000820000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 500. -/
noncomputable def rhs500 : Nat := 0x1b0000096c0000d80000024000024036d80000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked500 : reconX topRColumns 0x1804000800000001200940140058030004004000030 = rhs500 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 500. -/
theorem initialChecked500 : checkSearchInitial 8 180 12 rows500 lambdas500 0x401 0x1804000800000001200940140058030004004000030 rhs500 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 500 has a listed outside support. -/
theorem complete500 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800000001200940140058030004004000030)
    (hweight : bitCount 180 (outsideMask word 0x1804000800000001200940140058030004004000030) ≤ 1) :
    outsideMask word 0x1804000800000001200940140058030004004000030 ∈ allowed500 := by
  exact outside_mem_of_search 8 180 12 rows500 lambdas500 0x401 0x1804000800000001200940140058030004004000030 rhs500 1
    topEColumns topETransposeColumns tree500 allowed500 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked500 checked500
    hw (he.trans rhsChecked500) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 501. -/
noncomputable def lambdas501 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000004000008000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000008200000800000820000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 501. -/
noncomputable def rhs501 : Nat := 0x1b0000246c0000d80000024000024000000000b76

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked501 : reconX topRColumns 0x1804000800000004800340140118030004004000018 = rhs501 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 501. -/
theorem initialChecked501 : checkSearchInitial 8 180 12 rows501 lambdas501 0x400 0x1804000800000004800340140118030004004000018 rhs501 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 501 has a listed outside support. -/
theorem complete501 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800000004800340140118030004004000018)
    (hweight : bitCount 180 (outsideMask word 0x1804000800000004800340140118030004004000018) ≤ 1) :
    outsideMask word 0x1804000800000004800340140118030004004000018 ∈ allowed501 := by
  exact outside_mem_of_search 8 180 12 rows501 lambdas501 0x400 0x1804000800000004800340140118030004004000018 rhs501 1
    topEColumns topETransposeColumns tree501 allowed501 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked501 checked501
    hw (he.trans rhsChecked501) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 502. -/
noncomputable def lambdas502 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000010000000400000440000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000040001040000002000080400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 502. -/
noncomputable def rhs502 : Nat := 0x12000000480000d80000024036da4000db6000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked502 : reconX topRColumns 0x1804000800001200040b00100010030004004030006 = rhs502 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 502. -/
theorem initialChecked502 : checkSearchInitial 8 180 13 rows502 lambdas502 0x200 0x1804000800001200040b00100010030004004030006 rhs502 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 502 has a listed outside support. -/
theorem complete502 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800001200040b00100010030004004030006)
    (hweight : bitCount 180 (outsideMask word 0x1804000800001200040b00100010030004004030006) ≤ 1) :
    outsideMask word 0x1804000800001200040b00100010030004004030006 ∈ allowed502 := by
  exact outside_mem_of_search 8 180 13 rows502 lambdas502 0x200 0x1804000800001200040b00100010030004004030006 rhs502 1
    topEColumns topETransposeColumns tree502 allowed502 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked502 checked502
    hw (he.trans rhsChecked502) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 503. -/
noncomputable def lambdas503 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000100000004000004400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000004000008000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000200000a00000820000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 503. -/
noncomputable def rhs503 : Nat := 0x120000006c0000d80000024036da4000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked503 : reconX topRColumns 0x1804000800001200200b40100018030004004030000 = rhs503 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 503. -/
theorem initialChecked503 : checkSearchInitial 8 180 12 rows503 lambdas503 0x401 0x1804000800001200200b40100018030004004030000 rhs503 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 503 has a listed outside support. -/
theorem complete503 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1804000800001200200b40100018030004004030000)
    (hweight : bitCount 180 (outsideMask word 0x1804000800001200200b40100018030004004030000) ≤ 1) :
    outsideMask word 0x1804000800001200200b40100018030004004030000 ∈ allowed503 := by
  exact outside_mem_of_search 8 180 12 rows503 lambdas503 0x401 0x1804000800001200200b40100018030004004030000 rhs503 1
    topEColumns topETransposeColumns tree503 allowed503 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked503 checked503
    hw (he.trans rhsChecked503) hweight

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

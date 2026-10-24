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
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineSearchPart3

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData
open PackedDigits BB.Bravyi360 BB.Bravyi360.FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 304. -/
noncomputable def lambdas304 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000003000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 304. -/
noncomputable def rhs304 : Nat := 0x9000492000012000d80d80036240000000000249000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked304 : reconX topRColumns 0xfc01c0208000008000001000000000006200c00240 = rhs304 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 304. -/
theorem initialChecked304 : checkSearchInitial 8 180 10 rows304 lambdas304 0x44 0xfc01c0208000008000001000000000006200c00240 rhs304 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 304 has a listed outside support. -/
theorem complete304 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc01c0208000008000001000000000006200c00240)
    (hweight : bitCount 180 (outsideMask word 0xfc01c0208000008000001000000000006200c00240) ≤ 1) :
    outsideMask word 0xfc01c0208000008000001000000000006200c00240 ∈ allowed304 := by
  exact outside_mem_of_search 8 180 10 rows304 lambdas304 0x44 0xfc01c0208000008000001000000000006200c00240 rhs304 1
    topEColumns topETransposeColumns tree304 allowed304 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked304 checked304
    hw (he.trans rhsChecked304) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 305. -/
noncomputable def lambdas305 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 305. -/
noncomputable def rhs305 : Nat := 0x492000da40000006c0000fc0000264000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked305 : reconX topRColumns 0xfc02a0060000000000000000000006600e00300000 = rhs305 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 305. -/
theorem initialChecked305 : checkSearchInitial 8 180 10 rows305 lambdas305 0x40 0xfc02a0060000000000000000000006600e00300000 rhs305 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 305 has a listed outside support. -/
theorem complete305 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc02a0060000000000000000000006600e00300000)
    (hweight : bitCount 180 (outsideMask word 0xfc02a0060000000000000000000006600e00300000) ≤ 1) :
    outsideMask word 0xfc02a0060000000000000000000006600e00300000 ∈ allowed305 := by
  exact outside_mem_of_search 8 180 10 rows305 lambdas305 0x40 0xfc02a0060000000000000000000006600e00300000 rhs305 1
    topEColumns topETransposeColumns tree305 allowed305 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked305 checked305
    hw (he.trans rhsChecked305) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 306. -/
noncomputable def lambdas306 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 306. -/
noncomputable def rhs306 : Nat := 0x492000d80900000240000fc0000252000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked306 : reconX topRColumns 0xfc0310050000000000000000000006a00e00280000 = rhs306 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 306. -/
theorem initialChecked306 : checkSearchInitial 8 180 10 rows306 lambdas306 0x40 0xfc0310050000000000000000000006a00e00280000 rhs306 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 306 has a listed outside support. -/
theorem complete306 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc0310050000000000000000000006a00e00280000)
    (hweight : bitCount 180 (outsideMask word 0xfc0310050000000000000000000006a00e00280000) ≤ 1) :
    outsideMask word 0xfc0310050000000000000000000006a00e00280000 ∈ allowed306 := by
  exact outside_mem_of_search 8 180 10 rows306 lambdas306 0x40 0xfc0310050000000000000000000006a00e00280000 rhs306 1
    topEColumns topETransposeColumns tree306 allowed306 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked306 checked306
    hw (he.trans rhsChecked306) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 307. -/
noncomputable def lambdas307 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 307. -/
noncomputable def rhs307 : Nat := 0x27f000000240000000000000da4480000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked307 : reconX topRColumns 0x100000000000000ee01c401803c0008000000000180 = rhs307 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 307. -/
theorem initialChecked307 : checkSearchInitial 8 180 10 rows307 lambdas307 0x8 0x100000000000000ee01c401803c0008000000000180 rhs307 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 307 has a listed outside support. -/
theorem complete307 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x100000000000000ee01c401803c0008000000000180)
    (hweight : bitCount 180 (outsideMask word 0x100000000000000ee01c401803c0008000000000180) ≤ 1) :
    outsideMask word 0x100000000000000ee01c401803c0008000000000180 ∈ allowed307 := by
  exact outside_mem_of_search 8 180 10 rows307 lambdas307 0x8 0x100000000000000ee01c401803c0008000000000180 rhs307 1
    topEColumns topETransposeColumns tree307 allowed307 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked307 checked307
    hw (he.trans rhsChecked307) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 308. -/
noncomputable def lambdas308 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 308. -/
noncomputable def rhs308 : Nat := 0x4bf000000240000000000000936480009936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked308 : reconX topRColumns 0x1000000000000015e02c401805c0008000000000140 = rhs308 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 308. -/
theorem initialChecked308 : checkSearchInitial 8 180 10 rows308 lambdas308 0x8 0x1000000000000015e02c401805c0008000000000140 rhs308 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 308 has a listed outside support. -/
theorem complete308 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000000015e02c401805c0008000000000140)
    (hweight : bitCount 180 (outsideMask word 0x1000000000000015e02c401805c0008000000000140) ≤ 1) :
    outsideMask word 0x1000000000000015e02c401805c0008000000000140 ∈ allowed308 := by
  exact outside_mem_of_search 8 180 10 rows308 lambdas308 0x8 0x1000000000000015e02c401805c0008000000000140 rhs308 1
    topEColumns topETransposeColumns tree308 allowed308 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked308 checked308
    hw (he.trans rhsChecked308) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 309. -/
noncomputable def lambdas309 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 309. -/
noncomputable def rhs309 : Nat := 0x93f00000024000000000000001248001b936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked309 : reconX topRColumns 0x1000000000000023e04c401809c00080000000000c0 = rhs309 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 309. -/
theorem initialChecked309 : checkSearchInitial 8 180 10 rows309 lambdas309 0x8 0x1000000000000023e04c401809c00080000000000c0 rhs309 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 309 has a listed outside support. -/
theorem complete309 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000000023e04c401809c00080000000000c0)
    (hweight : bitCount 180 (outsideMask word 0x1000000000000023e04c401809c00080000000000c0) ≤ 1) :
    outsideMask word 0x1000000000000023e04c401809c00080000000000c0 ∈ allowed309 := by
  exact outside_mem_of_search 8 180 10 rows309 lambdas309 0x8 0x1000000000000023e04c401809c00080000000000c0 rhs309 1
    topEColumns topETransposeColumns tree309 allowed309 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked309 checked309
    hw (he.trans rhsChecked309) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 310. -/
noncomputable def lambdas310 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 310. -/
noncomputable def rhs310 : Nat := 0xfc90000002400000000000004a4d80012db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked310 : reconX topRColumns 0x100000000000003e207040180e40008000000000030 = rhs310 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 310. -/
theorem initialChecked310 : checkSearchInitial 8 180 10 rows310 lambdas310 0x8 0x100000000000003e207040180e40008000000000030 rhs310 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 310 has a listed outside support. -/
theorem complete310 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x100000000000003e207040180e40008000000000030)
    (hweight : bitCount 180 (outsideMask word 0x100000000000003e207040180e40008000000000030) ≤ 1) :
    outsideMask word 0x100000000000003e207040180e40008000000000030 ∈ allowed310 := by
  exact outside_mem_of_search 8 180 10 rows310 lambdas310 0x8 0x100000000000003e207040180e40008000000000030 rhs310 1
    topEColumns topETransposeColumns tree310 allowed310 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked310 checked310
    hw (he.trans rhsChecked310) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 311. -/
noncomputable def lambdas311 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 311. -/
noncomputable def rhs311 : Nat := 0x240000fc0000240000000000db6000492000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked311 : reconX topRColumns 0x1000000000000240f80380188038008000000006000 = rhs311 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 311. -/
theorem initialChecked311 : checkSearchInitial 8 180 10 rows311 lambdas311 0x2 0x1000000000000240f80380188038008000000006000 rhs311 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 311 has a listed outside support. -/
theorem complete311 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000000240f80380188038008000000006000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000000240f80380188038008000000006000) ≤ 1) :
    outsideMask word 0x1000000000000240f80380188038008000000006000 ∈ allowed311 := by
  exact outside_mem_of_search 8 180 10 rows311 lambdas311 0x2 0x1000000000000240f80380188038008000000006000 rhs311 1
    topEColumns topETransposeColumns tree311 allowed311 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked311 checked311
    hw (he.trans rhsChecked311) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 312. -/
noncomputable def lambdas312 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 312. -/
noncomputable def rhs312 : Nat := 0x480000fc000024000000000092400049b000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked312 : reconX topRColumns 0x1000000000000480f40380190038008000000005000 = rhs312 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 312. -/
theorem initialChecked312 : checkSearchInitial 8 180 10 rows312 lambdas312 0x2 0x1000000000000480f40380190038008000000005000 rhs312 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 312 has a listed outside support. -/
theorem complete312 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000000480f40380190038008000000005000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000000480f40380190038008000000005000) ≤ 1) :
    outsideMask word 0x1000000000000480f40380190038008000000005000 ∈ allowed312 := by
  exact outside_mem_of_search 8 180 10 rows312 lambdas312 0x2 0x1000000000000480f40380190038008000000005000 rhs312 1
    topEColumns topETransposeColumns tree312 allowed312 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked312 checked312
    hw (he.trans rhsChecked312) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 313. -/
noncomputable def lambdas313 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 313. -/
noncomputable def rhs313 : Nat := 0x900000fc0000240000000000000000489000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked313 : reconX topRColumns 0x1000000000000900ec03801a0038008000000003000 = rhs313 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 313. -/
theorem initialChecked313 : checkSearchInitial 8 180 10 rows313 lambdas313 0x2 0x1000000000000900ec03801a0038008000000003000 rhs313 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 313 has a listed outside support. -/
theorem complete313 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000000900ec03801a0038008000000003000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000000900ec03801a0038008000000003000) ≤ 1) :
    outsideMask word 0x1000000000000900ec03801a0038008000000003000 ∈ allowed313 := by
  exact outside_mem_of_search 8 180 10 rows313 lambdas313 0x2 0x1000000000000900ec03801a0038008000000003000 rhs313 1
    topEColumns topETransposeColumns tree313 allowed313 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked313 checked313
    hw (he.trans rhsChecked313) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 314. -/
noncomputable def lambdas314 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 314. -/
noncomputable def rhs314 : Nat := 0x9000000fc0000240000000036d80000492000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked314 : reconX topRColumns 0x1000000000001200dc03801c0038008000000030000 = rhs314 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 314. -/
theorem initialChecked314 : checkSearchInitial 8 180 10 rows314 lambdas314 0x8 0x1000000000001200dc03801c0038008000000030000 rhs314 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 314 has a listed outside support. -/
theorem complete314 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000001200dc03801c0038008000000030000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000001200dc03801c0038008000000030000) ≤ 1) :
    outsideMask word 0x1000000000001200dc03801c0038008000000030000 ∈ allowed314 := by
  exact outside_mem_of_search 8 180 10 rows314 lambdas314 0x8 0x1000000000001200dc03801c0038008000000030000 rhs314 1
    topEColumns topETransposeColumns tree314 allowed314 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked314 checked314
    hw (he.trans rhsChecked314) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 315. -/
noncomputable def lambdas315 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 315. -/
noncomputable def rhs315 : Nat := 0x900003f000000240000000036d80012480000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked315 : reconX topRColumns 0x1000000000001207c00c401c01c0008000000030000 = rhs315 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 315. -/
theorem initialChecked315 : checkSearchInitial 8 180 10 rows315 lambdas315 0x8 0x1000000000001207c00c401c01c0008000000030000 rhs315 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 315 has a listed outside support. -/
theorem complete315 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000001207c00c401c01c0008000000030000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000001207c00c401c01c0008000000030000) ≤ 1) :
    outsideMask word 0x1000000000001207c00c401c01c0008000000030000 ∈ allowed315 := by
  exact outside_mem_of_search 8 180 10 rows315 lambdas315 0x8 0x1000000000001207c00c401c01c0008000000030000 rhs315 1
    topEColumns topETransposeColumns tree315 allowed315 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked315 checked315
    hw (he.trans rhsChecked315) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 316. -/
noncomputable def lambdas316 : Nat := (Nat.lor 0x20000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000038a000004000000000000000000000004100000040000000000000000000000010e00000a000002000000000000000000100000020000000000000000000000010a00000e00000200000000000000000010000001 (Nat.shiftLeft 0x400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 316. -/
noncomputable def rhs316 : Nat := 0x12480000fc00002400000000240240006db000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked316 : reconX topRColumns 0x1000000000002080b4038011003800800000002d000 = rhs316 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 316. -/
theorem initialChecked316 : checkSearchInitial 8 180 21 rows316 lambdas316 0x4 0x1000000000002080b4038011003800800000002d000 rhs316 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 316 has a listed outside support. -/
theorem complete316 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000002080b4038011003800800000002d000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000002080b4038011003800800000002d000) ≤ 1) :
    outsideMask word 0x1000000000002080b4038011003800800000002d000 ∈ allowed316 := by
  exact outside_mem_of_search 8 180 21 rows316 lambdas316 0x4 0x1000000000002080b4038011003800800000002d000 rhs316 1
    topEColumns topETransposeColumns tree316 allowed316 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked316 checked316
    hw (he.trans rhsChecked316) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 317. -/
noncomputable def lambdas317 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000300000100000000000000000000000000000001000000000000000000000000020000000200000200000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 317. -/
noncomputable def rhs317 : Nat := 0x1248001b0000002400000000240240126c9000ff6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked317 : reconX topRColumns 0x10000000000020832804401100c000800000002d018 = rhs317 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 317. -/
theorem initialChecked317 : checkSearchInitial 8 180 11 rows317 lambdas317 0x2 0x10000000000020832804401100c000800000002d018 rhs317 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 317 has a listed outside support. -/
theorem complete317 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000020832804401100c000800000002d018)
    (hweight : bitCount 180 (outsideMask word 0x10000000000020832804401100c000800000002d018) ≤ 1) :
    outsideMask word 0x10000000000020832804401100c000800000002d018 ∈ allowed317 := by
  exact outside_mem_of_search 8 180 11 rows317 lambdas317 0x2 0x10000000000020832804401100c000800000002d018 rhs317 1
    topEColumns topETransposeColumns tree317 allowed317 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked317 checked317
    hw (he.trans rhsChecked317) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 318. -/
noncomputable def lambdas318 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000800000804000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000028000030c400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000200000308000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 318. -/
noncomputable def rhs318 : Nat := 0x12000009fc0000240000000024900036b52000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked318 : reconX topRColumns 0x10000000000024019c0180100078008000000028030 = rhs318 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 318. -/
theorem initialChecked318 : checkSearchInitial 8 180 14 rows318 lambdas318 0x12 0x10000000000024019c0180100078008000000028030 rhs318 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 318 has a listed outside support. -/
theorem complete318 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000024019c0180100078008000000028030)
    (hweight : bitCount 180 (outsideMask word 0x10000000000024019c0180100078008000000028030) ≤ 1) :
    outsideMask word 0x10000000000024019c0180100078008000000028030 ∈ allowed318 := by
  exact outside_mem_of_search 8 180 14 rows318 lambdas318 0x12 0x10000000000024019c0180100078008000000028030 rhs318 1
    topEColumns topETransposeColumns tree318 allowed318 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked318 checked318
    hw (he.trans rhsChecked318) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 319. -/
noncomputable def lambdas319 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000300000100000000000000000000000000000001000000000000000000000000020000000200000200000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 319. -/
noncomputable def rhs319 : Nat := 0x1200025b000000240000000024900da46c0000ff6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked319 : reconX topRColumns 0x100000000000240a2014401002c0008000000028198 = rhs319 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 319. -/
theorem initialChecked319 : checkSearchInitial 8 180 11 rows319 lambdas319 0x2 0x100000000000240a2014401002c0008000000028198 rhs319 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 319 has a listed outside support. -/
theorem complete319 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x100000000000240a2014401002c0008000000028198)
    (hweight : bitCount 180 (outsideMask word 0x100000000000240a2014401002c0008000000028198) ≤ 1) :
    outsideMask word 0x100000000000240a2014401002c0008000000028198 ∈ allowed319 := by
  exact outside_mem_of_search 8 180 11 rows319 lambdas319 0x2 0x100000000000240a2014401002c0008000000028198 rhs319 1
    topEColumns topETransposeColumns tree319 allowed319 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked319 checked319
    hw (he.trans rhsChecked319) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 320. -/
noncomputable def lambdas320 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000300000100000000000000000000000000000001000000000000000000000000020000000200000200000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 320. -/
noncomputable def rhs320 : Nat := 0x1200049b0000002400000000249009366c0009ff6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked320 : reconX topRColumns 0x10000000000024112024401004c0008000000028158 = rhs320 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 320. -/
theorem initialChecked320 : checkSearchInitial 8 180 11 rows320 lambdas320 0x2 0x10000000000024112024401004c0008000000028158 rhs320 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 320 has a listed outside support. -/
theorem complete320 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000024112024401004c0008000000028158)
    (hweight : bitCount 180 (outsideMask word 0x10000000000024112024401004c0008000000028158) ≤ 1) :
    outsideMask word 0x10000000000024112024401004c0008000000028158 ∈ allowed320 := by
  exact outside_mem_of_search 8 180 11 rows320 lambdas320 0x2 0x10000000000024112024401004c0008000000028158 rhs320 1
    topEColumns topETransposeColumns tree320 allowed320 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked320 checked320
    hw (he.trans rhsChecked320) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 321. -/
noncomputable def lambdas321 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000002000000800000020000000000000000000000010000000000000000000000000080000082000000000000000200000008000000800000000000000000000000030000000400000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 321. -/
noncomputable def rhs321 : Nat := 0x122400006c00002400000000244b60006d2000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked321 : reconX topRColumns 0x100000000000264028028010801800800000002e003 = rhs321 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 321. -/
theorem initialChecked321 : checkSearchInitial 8 180 11 rows321 lambdas321 0x3 0x100000000000264028028010801800800000002e003 rhs321 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 321 has a listed outside support. -/
theorem complete321 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x100000000000264028028010801800800000002e003)
    (hweight : bitCount 180 (outsideMask word 0x100000000000264028028010801800800000002e003) ≤ 1) :
    outsideMask word 0x100000000000264028028010801800800000002e003 ∈ allowed321 := by
  exact outside_mem_of_search 8 180 11 rows321 lambdas321 0x3 0x100000000000264028028010801800800000002e003 rhs321 1
    topEColumns topETransposeColumns tree321 allowed321 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked321 checked321
    hw (he.trans rhsChecked321) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 322. -/
noncomputable def lambdas322 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 322. -/
noncomputable def rhs322 : Nat := 0x12fc0000000000240000000024d92000252000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked322 : reconX topRColumns 0x1000000000002bc05c0240138000008000000028000 = rhs322 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 322. -/
theorem initialChecked322 : checkSearchInitial 8 180 9 rows322 lambdas322 0x8 0x1000000000002bc05c0240138000008000000028000 rhs322 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 322 has a listed outside support. -/
theorem complete322 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000002bc05c0240138000008000000028000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000002bc05c0240138000008000000028000) ≤ 1) :
    outsideMask word 0x1000000000002bc05c0240138000008000000028000 ∈ allowed322 := by
  exact outside_mem_of_search 8 180 9 rows322 lambdas322 0x8 0x1000000000002bc05c0240138000008000000028000 rhs322 1
    topEColumns topETransposeColumns tree322 allowed322 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked322 checked322
    hw (he.trans rhsChecked322) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 323. -/
noncomputable def lambdas323 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000001020000020000020000000000000000080400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000010000008000000200000000000000000800000804

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 323. -/
noncomputable def rhs323 : Nat := 0x1b000000b40000240000000012480000ff6000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked323 : reconX topRColumns 0x1000000000003600d40300140028008000000018005 = rhs323 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 323. -/
theorem initialChecked323 : checkSearchInitial 8 180 15 rows323 lambdas323 0x5 0x1000000000003600d40300140028008000000018005 rhs323 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 323 has a listed outside support. -/
theorem complete323 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000003600d40300140028008000000018005)
    (hweight : bitCount 180 (outsideMask word 0x1000000000003600d40300140028008000000018005) ≤ 1) :
    outsideMask word 0x1000000000003600d40300140028008000000018005 ∈ allowed323 := by
  exact outside_mem_of_search 8 180 15 rows323 lambdas323 0x5 0x1000000000003600d40300140028008000000018005 rhs323 1
    topEColumns topETransposeColumns tree323 allowed323 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked323 checked323
    hw (he.trans rhsChecked323) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 324. -/
noncomputable def lambdas324 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000300000004000000800000000000000000000000208000000000000000000000010000010400000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 324. -/
noncomputable def rhs324 : Nat := 0x1b0000094800002400000000124800366e4000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked324 : reconX topRColumns 0x10000000000036010800c0140050008000000018035 = rhs324 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 324. -/
theorem initialChecked324 : checkSearchInitial 8 180 10 rows324 lambdas324 0x2 0x10000000000036010800c0140050008000000018035 rhs324 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 324 has a listed outside support. -/
theorem complete324 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000036010800c0140050008000000018035)
    (hweight : bitCount 180 (outsideMask word 0x10000000000036010800c0140050008000000018035) ≤ 1) :
    outsideMask word 0x10000000000036010800c0140050008000000018035 ∈ allowed324 := by
  exact outside_mem_of_search 8 180 10 rows324 lambdas324 0x2 0x10000000000036010800c0140050008000000018035 rhs324 1
    topEColumns topETransposeColumns tree324 allowed324 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked324 checked324
    hw (he.trans rhsChecked324) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 325. -/
noncomputable def lambdas325 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000003000000040000008000000000000000000000082080000000000000000000000100004104000000400000000000000000000000020000000200000200000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 325. -/
noncomputable def rhs325 : Nat := 0x1b000249000000240000000012480d80fc0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked325 : reconX topRColumns 0x10000000000036084010401402400080000000181b0 = rhs325 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 325. -/
theorem initialChecked325 : checkSearchInitial 8 180 11 rows325 lambdas325 0x4 0x10000000000036084010401402400080000000181b0 rhs325 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 325 has a listed outside support. -/
theorem complete325 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000036084010401402400080000000181b0)
    (hweight : bitCount 180 (outsideMask word 0x10000000000036084010401402400080000000181b0) ≤ 1) :
    outsideMask word 0x10000000000036084010401402400080000000181b0 ∈ allowed325 := by
  exact outside_mem_of_search 8 180 11 rows325 lambdas325 0x4 0x10000000000036084010401402400080000000181b0 rhs325 1
    topEColumns topETransposeColumns tree325 allowed325 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked325 checked325
    hw (he.trans rhsChecked325) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 326. -/
noncomputable def lambdas326 : Nat := (Nat.lor 0x20000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000020e0000060000020000000000000000002000000400000000000000000000000386000008000000000000000000000008200000020000000000000000000000020600000e00000200000000000000000020000001 (Nat.shiftLeft 0x8000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 326. -/
noncomputable def rhs326 : Nat := 0x24900000fc0000240000000000000000249000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked326 : reconX topRColumns 0x10000000000041006c03800a003800800000001b000 = rhs326 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 326. -/
theorem initialChecked326 : checkSearchInitial 8 180 19 rows326 lambdas326 0x1 0x10000000000041006c03800a003800800000001b000 rhs326 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 326 has a listed outside support. -/
theorem complete326 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000041006c03800a003800800000001b000)
    (hweight : bitCount 180 (outsideMask word 0x10000000000041006c03800a003800800000001b000) ≤ 1) :
    outsideMask word 0x10000000000041006c03800a003800800000001b000 ∈ allowed326 := by
  exact outside_mem_of_search 8 180 19 rows326 lambdas326 0x1 0x10000000000041006c03800a003800800000001b000 rhs326 1
    topEColumns topETransposeColumns tree326 allowed326 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked326 checked326
    hw (he.trans rhsChecked326) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 327. -/
noncomputable def lambdas327 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 327. -/
noncomputable def rhs327 : Nat := 0x24fc00000000002400000000004920006d2000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked327 : reconX topRColumns 0x10000000000047c09c02400b8000008000000018000 = rhs327 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 327. -/
theorem initialChecked327 : checkSearchInitial 8 180 9 rows327 lambdas327 0x8 0x10000000000047c09c02400b8000008000000018000 rhs327 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 327 has a listed outside support. -/
theorem complete327 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000047c09c02400b8000008000000018000)
    (hweight : bitCount 180 (outsideMask word 0x10000000000047c09c02400b8000008000000018000) ≤ 1) :
    outsideMask word 0x10000000000047c09c02400b8000008000000018000 ∈ allowed327 := by
  exact outside_mem_of_search 8 180 9 rows327 lambdas327 0x8 0x10000000000047c09c02400b8000008000000018000 rhs327 1
    topEColumns topETransposeColumns tree327 allowed327 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked327 checked327
    hw (he.trans rhsChecked327) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 328. -/
noncomputable def lambdas328 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000018000030c400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000100000304000001000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 328. -/
noncomputable def rhs328 : Nat := 0x24000009fc0000240000000000000036fd2000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked328 : reconX topRColumns 0x10000000000048015c0180080078008000000018030 = rhs328 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 328. -/
theorem initialChecked328 : checkSearchInitial 8 180 13 rows328 lambdas328 0x10 0x10000000000048015c0180080078008000000018030 rhs328 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 328 has a listed outside support. -/
theorem complete328 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000048015c0180080078008000000018030)
    (hweight : bitCount 180 (outsideMask word 0x10000000000048015c0180080078008000000018030) ≤ 1) :
    outsideMask word 0x10000000000048015c0180080078008000000018030 ∈ allowed328 := by
  exact outside_mem_of_search 8 180 13 rows328 lambdas328 0x10 0x10000000000048015c0180080078008000000018030 rhs328 1
    topEColumns topETransposeColumns tree328 allowed328 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked328 checked328
    hw (he.trans rhsChecked328) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 329. -/
noncomputable def lambdas329 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000038000000840000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 329. -/
noncomputable def rhs329 : Nat := 0x2d000000fc0000240000000036d80000252000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked329 : reconX topRColumns 0x1000000000005a005c03800c0038008000000028000 = rhs329 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 329. -/
theorem initialChecked329 : checkSearchInitial 8 180 11 rows329 lambdas329 0x1 0x1000000000005a005c03800c0038008000000028000 rhs329 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 329 has a listed outside support. -/
theorem complete329 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000005a005c03800c0038008000000028000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000005a005c03800c0038008000000028000) ≤ 1) :
    outsideMask word 0x1000000000005a005c03800c0038008000000028000 ∈ allowed329 := by
  exact outside_mem_of_search 8 180 11 rows329 lambdas329 0x1 0x1000000000005a005c03800c0038008000000028000 rhs329 1
    topEColumns topETransposeColumns tree329 allowed329 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked329 checked329
    hw (he.trans rhsChecked329) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 330. -/
noncomputable def lambdas330 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000003800000084000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 330. -/
noncomputable def rhs330 : Nat := 0x2d00003f000000240000000036d80012240000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked330 : reconX topRColumns 0x1000000000005a07400c400c01c0008000000028000 = rhs330 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 330. -/
theorem initialChecked330 : checkSearchInitial 8 180 13 rows330 lambdas330 0x4 0x1000000000005a07400c400c01c0008000000028000 rhs330 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 330 has a listed outside support. -/
theorem complete330 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000005a07400c400c01c0008000000028000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000005a07400c400c01c0008000000028000) ≤ 1) :
    outsideMask word 0x1000000000005a07400c400c01c0008000000028000 ∈ allowed330 := by
  exact outside_mem_of_search 8 180 13 rows330 lambdas330 0x4 0x1000000000005a07400c400c01c0008000000028000 rhs330 1
    topEColumns topETransposeColumns tree330 allowed330 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked330 checked330
    hw (he.trans rhsChecked330) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 331. -/
noncomputable def lambdas331 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000003080000040000000000000000000000000000000400000000000000000000000304000008000000000000000000000000000000020000000000000000000000030000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 331. -/
noncomputable def rhs331 : Nat := 0x36d80000fc0000240000000024024000000000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked331 : reconX topRColumns 0x1000000000006180240380030038008000000036000 = rhs331 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 331. -/
theorem initialChecked331 : checkSearchInitial 8 180 15 rows331 lambdas331 0x4 0x1000000000006180240380030038008000000036000 rhs331 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 331 has a listed outside support. -/
theorem complete331 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000006180240380030038008000000036000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000006180240380030038008000000036000) ≤ 1) :
    outsideMask word 0x1000000000006180240380030038008000000036000 ∈ allowed331 := by
  exact outside_mem_of_search 8 180 15 rows331 lambdas331 0x4 0x1000000000006180240380030038008000000036000 rhs331 1
    topEColumns topETransposeColumns tree331 allowed331 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked331 checked331
    hw (he.trans rhsChecked331) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 332. -/
noncomputable def lambdas332 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 332. -/
noncomputable def rhs332 : Nat := 0x36fc0000000000240000000024d92000492000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked332 : reconX topRColumns 0x10000000000063c0dc0240038000008000000030000 = rhs332 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 332. -/
theorem initialChecked332 : checkSearchInitial 8 180 10 rows332 lambdas332 0x8 0x10000000000063c0dc0240038000008000000030000 rhs332 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 332 has a listed outside support. -/
theorem complete332 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000063c0dc0240038000008000000030000)
    (hweight : bitCount 180 (outsideMask word 0x10000000000063c0dc0240038000008000000030000) ≤ 1) :
    outsideMask word 0x10000000000063c0dc0240038000008000000030000 ∈ allowed332 := by
  exact outside_mem_of_search 8 180 10 rows332 lambdas332 0x8 0x10000000000063c0dc0240038000008000000030000 rhs332 1
    topEColumns topETransposeColumns tree332 allowed332 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked332 checked332
    hw (he.trans rhsChecked332) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 333. -/
noncomputable def lambdas333 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000106000002000002000000000000000000040000000000000000000000000800020a0000020000020000000000001000000200000000000000000000000000000308000004000000000000000000000000000000040000000000000000000000030000000c00000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 333. -/
noncomputable def rhs333 : Nat := 0x36900000fc0000240000000024900000009000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked333 : reconX topRColumns 0x10000000000065002c0380020038008000000033000 = rhs333 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 333. -/
theorem initialChecked333 : checkSearchInitial 8 180 14 rows333 lambdas333 0xa 0x10000000000065002c0380020038008000000033000 rhs333 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 333 has a listed outside support. -/
theorem complete333 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000065002c0380020038008000000033000)
    (hweight : bitCount 180 (outsideMask word 0x10000000000065002c0380020038008000000033000) ≤ 1) :
    outsideMask word 0x10000000000065002c0380020038008000000033000 ∈ allowed333 := by
  exact outside_mem_of_search 8 180 14 rows333 lambdas333 0xa 0x10000000000065002c0380020038008000000033000 rhs333 1
    topEColumns topETransposeColumns tree333 allowed333 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked333 checked333
    hw (he.trans rhsChecked333) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 334. -/
noncomputable def lambdas334 : Nat := (Nat.lor 0x2000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000004000106000002000002000000000000200000040000000000000000000000000000020a00000200000200000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000030000000c00000000000000000000000000000001 (Nat.shiftLeft 0x400000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 334. -/
noncomputable def rhs334 : Nat := 0x36480000fc000024000000002402400001b000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked334 : reconX topRColumns 0x1000000000006880340380010038008000000035000 = rhs334 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 334. -/
theorem initialChecked334 : checkSearchInitial 8 180 18 rows334 lambdas334 0x10 0x1000000000006880340380010038008000000035000 rhs334 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 334 has a listed outside support. -/
theorem complete334 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000006880340380010038008000000035000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000006880340380010038008000000035000) ≤ 1) :
    outsideMask word 0x1000000000006880340380010038008000000035000 ∈ allowed334 := by
  exact outside_mem_of_search 8 180 18 rows334 lambdas334 0x10 0x1000000000006880340380010038008000000035000 rhs334 1
    topEColumns topETransposeColumns tree334 allowed334 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked334 checked334
    hw (he.trans rhsChecked334) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 335. -/
noncomputable def lambdas335 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000004000184000002000002000000000008200001000000000000000000000000000400010600000200000200000000000020000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000030000000400000000000000000000000200000001 (Nat.shiftLeft 0x40000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 335. -/
noncomputable def rhs335 : Nat := 0x364800006c000024000000002402400001b000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked335 : reconX topRColumns 0x1000000000006880a40280010018008000000035003 = rhs335 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 335. -/
theorem initialChecked335 : checkSearchInitial 8 180 17 rows335 lambdas335 0x18 0x1000000000006880a40280010018008000000035003 rhs335 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 335 has a listed outside support. -/
theorem complete335 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000006880a40280010018008000000035003)
    (hweight : bitCount 180 (outsideMask word 0x1000000000006880a40280010018008000000035003) ≤ 1) :
    outsideMask word 0x1000000000006880a40280010018008000000035003 ∈ allowed335 := by
  exact outside_mem_of_search 8 180 17 rows335 lambdas335 0x18 0x1000000000006880a40280010018008000000035003 rhs335 1
    topEColumns topETransposeColumns tree335 allowed335 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked335 checked335
    hw (he.trans rhsChecked335) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 336. -/
noncomputable def lambdas336 : Nat := 0x80000080400000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000380000308800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000280000008000001000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 336. -/
noncomputable def rhs336 : Nat := 0x36000009fc0000240000000024900036d92000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked336 : reconX topRColumns 0x1000000000006c011c0180000078008000000030030 = rhs336 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 336. -/
theorem initialChecked336 : checkSearchInitial 8 180 11 rows336 lambdas336 0x12 0x1000000000006c011c0180000078008000000030030 rhs336 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 336 has a listed outside support. -/
theorem complete336 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000006c011c0180000078008000000030030)
    (hweight : bitCount 180 (outsideMask word 0x1000000000006c011c0180000078008000000030030) ≤ 1) :
    outsideMask word 0x1000000000006c011c0180000078008000000030030 ∈ allowed336 := by
  exact outside_mem_of_search 8 180 11 rows336 lambdas336 0x12 0x1000000000006c011c0180000078008000000030030 rhs336 1
    topEColumns topETransposeColumns tree336 allowed336 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked336 checked336
    hw (he.trans rhsChecked336) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 337. -/
noncomputable def lambdas337 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 337. -/
noncomputable def rhs337 : Nat := 0x3fd80000000000240000000012da4000492000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked337 : reconX topRColumns 0x1000000000007380f80240070000008000000006000 = rhs337 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 337. -/
theorem initialChecked337 : checkSearchInitial 8 180 11 rows337 lambdas337 0x10 0x1000000000007380f80240070000008000000006000 rhs337 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 337 has a listed outside support. -/
theorem complete337 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007380f80240070000008000000006000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007380f80240070000008000000006000) ≤ 1) :
    outsideMask word 0x1000000000007380f80240070000008000000006000 ∈ allowed337 := by
  exact outside_mem_of_search 8 180 11 rows337 lambdas337 0x10 0x1000000000007380f80240070000008000000006000 rhs337 1
    topEColumns topETransposeColumns tree337 allowed337 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked337 checked337
    hw (he.trans rhsChecked337) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 338. -/
noncomputable def lambdas338 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 338. -/
noncomputable def rhs338 : Nat := 0x3fb4000000000024000000001293600049b000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked338 : reconX topRColumns 0x1000000000007540f40240068000008000000005000 = rhs338 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 338. -/
theorem initialChecked338 : checkSearchInitial 8 180 12 rows338 lambdas338 0x20 0x1000000000007540f40240068000008000000005000 rhs338 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 338 has a listed outside support. -/
theorem complete338 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007540f40240068000008000000005000)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007540f40240068000008000000005000) ≤ 1) :
    outsideMask word 0x1000000000007540f40240068000008000000005000 ∈ allowed338 := by
  exact outside_mem_of_search 8 180 12 rows338 lambdas338 0x20 0x1000000000007540f40240068000008000000005000 rhs338 1
    topEColumns topETransposeColumns tree338 allowed338 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked338 checked338
    hw (he.trans rhsChecked338) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 339. -/
noncomputable def lambdas339 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000030000000000000880

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 339. -/
noncomputable def rhs339 : Nat := 0x3f900000b4000024000000001248000092d000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked339 : reconX topRColumns 0x1000000000007700440300060028008000000003005 = rhs339 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 339. -/
theorem initialChecked339 : checkSearchInitial 8 180 12 rows339 lambdas339 0x21 0x1000000000007700440300060028008000000003005 rhs339 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 339 has a listed outside support. -/
theorem complete339 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007700440300060028008000000003005)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007700440300060028008000000003005) ≤ 1) :
    outsideMask word 0x1000000000007700440300060028008000000003005 ∈ allowed339 := by
  exact outside_mem_of_search 8 180 12 rows339 lambdas339 0x21 0x1000000000007700440300060028008000000003005 rhs339 1
    topEColumns topETransposeColumns tree339 allowed339 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked339 checked339
    hw (he.trans rhsChecked339) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 340. -/
noncomputable def lambdas340 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 340. -/
noncomputable def rhs340 : Nat := 0x3f6c0000000000240000000012012000489000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked340 : reconX topRColumns 0x10000000000078c0ec0240058000008000000003000 = rhs340 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 340. -/
theorem initialChecked340 : checkSearchInitial 8 180 12 rows340 lambdas340 0x20 0x10000000000078c0ec0240058000008000000003000 rhs340 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 340 has a listed outside support. -/
theorem complete340 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000000000078c0ec0240058000008000000003000)
    (hweight : bitCount 180 (outsideMask word 0x10000000000078c0ec0240058000008000000003000) ≤ 1) :
    outsideMask word 0x10000000000078c0ec0240058000008000000003000 ∈ allowed340 := by
  exact outside_mem_of_search 8 180 12 rows340 lambdas340 0x20 0x10000000000078c0ec0240058000008000000003000 rhs340 1
    topEColumns topETransposeColumns tree340 allowed340 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked340 checked340
    hw (he.trans rhsChecked340) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 341. -/
noncomputable def lambdas341 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000030000000000000880

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 341. -/
noncomputable def rhs341 : Nat := 0x3f240000b40000240000000012936000936000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked341 : reconX topRColumns 0x1000000000007c40500300048028008000000006005 = rhs341 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 341. -/
theorem initialChecked341 : checkSearchInitial 8 180 12 rows341 lambdas341 0x21 0x1000000000007c40500300048028008000000006005 rhs341 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 341 has a listed outside support. -/
theorem complete341 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007c40500300048028008000000006005)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007c40500300048028008000000006005) ≤ 1) :
    outsideMask word 0x1000000000007c40500300048028008000000006005 ∈ allowed341 := by
  exact outside_mem_of_search 8 180 12 rows341 lambdas341 0x21 0x1000000000007c40500300048028008000000006005 rhs341 1
    topEColumns topETransposeColumns tree341 allowed341 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked341 checked341
    hw (he.trans rhsChecked341) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 342. -/
noncomputable def lambdas342 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000308000000000000000000000000000002010000000000000000000000000000208000000000000000000000010000020000000840

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 342. -/
noncomputable def rhs342 : Nat := 0x3f000009900000240000000012480036900000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked342 : reconX topRColumns 0x1000000000007e01500140040060008000000000033 = rhs342 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 342. -/
theorem initialChecked342 : checkSearchInitial 8 180 12 rows342 lambdas342 0x20 0x1000000000007e01500140040060008000000000033 rhs342 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 342 has a listed outside support. -/
theorem complete342 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e01500140040060008000000000033)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e01500140040060008000000000033) ≤ 1) :
    outsideMask word 0x1000000000007e01500140040060008000000000033 ∈ allowed342 := by
  exact outside_mem_of_search 8 180 12 rows342 lambdas342 0x20 0x1000000000007e01500140040060008000000000033 rhs342 1
    topEColumns topETransposeColumns tree342 allowed342 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked342 checked342
    hw (he.trans rhsChecked342) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 343. -/
noncomputable def lambdas343 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000304000000000000000000000000000002010000000000000000000000000000208000000000000000000000010000020000000840

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 343. -/
noncomputable def rhs343 : Nat := 0x3f000009480000240000000012480036024000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked343 : reconX topRColumns 0x1000000000007e018800c0040050008000000000035 = rhs343 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 343. -/
theorem initialChecked343 : checkSearchInitial 8 180 12 rows343 lambdas343 0x20 0x1000000000007e018800c0040050008000000000035 rhs343 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 343 has a listed outside support. -/
theorem complete343 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e018800c0040050008000000000035)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e018800c0040050008000000000035) ≤ 1) :
    outsideMask word 0x1000000000007e018800c0040050008000000000035 ∈ allowed343 := by
  exact outside_mem_of_search 8 180 12 rows343 lambdas343 0x20 0x1000000000007e018800c0040050008000000000035 rhs343 1
    topEColumns topETransposeColumns tree343 allowed343 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked343 checked343
    hw (he.trans rhsChecked343) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 344. -/
noncomputable def lambdas344 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 344. -/
noncomputable def rhs344 : Nat := 0x3f000036000000240000000012480024d80000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked344 : reconX topRColumns 0x1000000000007e06200e40040180008000000000030 = rhs344 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 344. -/
theorem initialChecked344 : checkSearchInitial 8 180 11 rows344 lambdas344 0x10 0x1000000000007e06200e40040180008000000000030 rhs344 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 344 has a listed outside support. -/
theorem complete344 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e06200e40040180008000000000030)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e06200e40040180008000000000030) ≤ 1) :
    outsideMask word 0x1000000000007e06200e40040180008000000000030 ∈ allowed344 := by
  exact outside_mem_of_search 8 180 11 rows344 lambdas344 0x10 0x1000000000007e06200e40040180008000000000030 rhs344 1
    topEColumns topETransposeColumns tree344 allowed344 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked344 checked344
    hw (he.trans rhsChecked344) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 345. -/
noncomputable def lambdas345 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000008000008200000000000000000400000000000021

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 345. -/
noncomputable def rhs345 : Nat := 0x3f000249000000240000000012480d80900000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked345 : reconX topRColumns 0x1000000000007e08c010400402400080000000001b0 = rhs345 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 345. -/
theorem initialChecked345 : checkSearchInitial 8 180 12 rows345 lambdas345 0x20 0x1000000000007e08c010400402400080000000001b0 rhs345 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 345 has a listed outside support. -/
theorem complete345 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e08c010400402400080000000001b0)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e08c010400402400080000000001b0) ≤ 1) :
    outsideMask word 0x1000000000007e08c010400402400080000000001b0 ∈ allowed345 := by
  exact outside_mem_of_search 8 180 12 rows345 lambdas345 0x20 0x1000000000007e08c010400402400080000000001b0 rhs345 1
    topEColumns topETransposeColumns tree345 allowed345 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked345 checked345
    hw (he.trans rhsChecked345) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 346. -/
noncomputable def lambdas346 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 346. -/
noncomputable def rhs346 : Nat := 0x3f000240000000240000000012480db6480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked346 : reconX topRColumns 0x1000000000007e09e01240040200008000000000180 = rhs346 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 346. -/
theorem initialChecked346 : checkSearchInitial 8 180 11 rows346 lambdas346 0x10 0x1000000000007e09e01240040200008000000000180 rhs346 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 346 has a listed outside support. -/
theorem complete346 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e09e01240040200008000000000180)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e09e01240040200008000000000180) ≤ 1) :
    outsideMask word 0x1000000000007e09e01240040200008000000000180 ∈ allowed346 := by
  exact outside_mem_of_search 8 180 11 rows346 lambdas346 0x10 0x1000000000007e09e01240040200008000000000180 rhs346 1
    topEColumns topETransposeColumns tree346 allowed346 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked346 checked346
    hw (he.trans rhsChecked346) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 347. -/
noncomputable def lambdas347 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 347. -/
noncomputable def rhs347 : Nat := 0x3f000480000000240000000012480924480009db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked347 : reconX topRColumns 0x1000000000007e12e02240040400008000000000140 = rhs347 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 347. -/
theorem initialChecked347 : checkSearchInitial 8 180 11 rows347 lambdas347 0x10 0x1000000000007e12e02240040400008000000000140 rhs347 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 347 has a listed outside support. -/
theorem complete347 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e12e02240040400008000000000140)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e12e02240040400008000000000140) ≤ 1) :
    outsideMask word 0x1000000000007e12e02240040400008000000000140 ∈ allowed347 := by
  exact outside_mem_of_search 8 180 11 rows347 lambdas347 0x10 0x1000000000007e12e02240040400008000000000140 rhs347 1
    topEColumns topETransposeColumns tree347 allowed347 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked347 checked347
    hw (he.trans rhsChecked347) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 348. -/
noncomputable def lambdas348 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 348. -/
noncomputable def rhs348 : Nat := 0x3f00090000000024000000001248000048001bdb6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked348 : reconX topRColumns 0x1000000000007e24e042400408000080000000000c0 = rhs348 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 348. -/
theorem initialChecked348 : checkSearchInitial 8 180 11 rows348 lambdas348 0x10 0x1000000000007e24e042400408000080000000000c0 rhs348 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 348 has a listed outside support. -/
theorem complete348 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e24e042400408000080000000000c0)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e24e042400408000080000000000c0) ≤ 1) :
    outsideMask word 0x1000000000007e24e042400408000080000000000c0 ∈ allowed348 := by
  exact outside_mem_of_search 8 180 11 rows348 lambdas348 0x10 0x1000000000007e24e042400408000080000000000c0 rhs348 1
    topEColumns topETransposeColumns tree348 allowed348 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked348 checked348
    hw (he.trans rhsChecked348) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 349. -/
noncomputable def lambdas349 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 349. -/
noncomputable def rhs349 : Nat := 0x3f0090000000002400000000124b6d80480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked349 : reconX topRColumns 0x1000000000007e48e08240041000008000000000c00 = rhs349 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 349. -/
theorem initialChecked349 : checkSearchInitial 8 180 11 rows349 lambdas349 0x10 0x1000000000007e48e08240041000008000000000c00 rhs349 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 349 has a listed outside support. -/
theorem complete349 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e48e08240041000008000000000c00)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e48e08240041000008000000000c00) ≤ 1) :
    outsideMask word 0x1000000000007e48e08240041000008000000000c00 ∈ allowed349 := by
  exact outside_mem_of_search 8 180 11 rows349 lambdas349 0x10 0x1000000000007e48e08240041000008000000000c00 rhs349 1
    topEColumns topETransposeColumns tree349 allowed349 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked349 checked349
    hw (he.trans rhsChecked349) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 350. -/
noncomputable def lambdas350 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 350. -/
noncomputable def rhs350 : Nat := 0x3f0120000000002400000000124a4900480240db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked350 : reconX topRColumns 0x1000000000007e90e10240042000008000000000a00 = rhs350 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 350. -/
theorem initialChecked350 : checkSearchInitial 8 180 11 rows350 lambdas350 0x10 0x1000000000007e90e10240042000008000000000a00 rhs350 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 350 has a listed outside support. -/
theorem complete350 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007e90e10240042000008000000000a00)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007e90e10240042000008000000000a00) ≤ 1) :
    outsideMask word 0x1000000000007e90e10240042000008000000000a00 ∈ allowed350 := by
  exact outside_mem_of_search 8 180 11 rows350 lambdas350 0x10 0x1000000000007e90e10240042000008000000000a00 rhs350 1
    topEColumns topETransposeColumns tree350 allowed350 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked350 checked350
    hw (he.trans rhsChecked350) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 351. -/
noncomputable def lambdas351 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 351. -/
noncomputable def rhs351 : Nat := 0x3f0240000000002400000000124800004806c0db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked351 : reconX topRColumns 0x1000000000007f20e20240044000008000000000600 = rhs351 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 351. -/
theorem initialChecked351 : checkSearchInitial 8 180 11 rows351 lambdas351 0x10 0x1000000000007f20e20240044000008000000000600 rhs351 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 351 has a listed outside support. -/
theorem complete351 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000000000007f20e20240044000008000000000600)
    (hweight : bitCount 180 (outsideMask word 0x1000000000007f20e20240044000008000000000600) ≤ 1) :
    outsideMask word 0x1000000000007f20e20240044000008000000000600 ∈ allowed351 := by
  exact outside_mem_of_search 8 180 11 rows351 lambdas351 0x10 0x1000000000007f20e20240044000008000000000600 rhs351 1
    topEColumns topETransposeColumns tree351 allowed351 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked351 checked351
    hw (he.trans rhsChecked351) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 352. -/
noncomputable def lambdas352 : Nat := 0x20000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000080000002000002200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000020000008000000200000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 352. -/
noncomputable def rhs352 : Nat := 0x1b00000000092424092d00001b4800006c0000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked352 : reconX topRColumns 0x1000012010001600600240140000008140140008010 = rhs352 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 352. -/
theorem initialChecked352 : checkSearchInitial 8 180 11 rows352 lambdas352 0x4 0x1000012010001600600240140000008140140008010 rhs352 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 352 has a listed outside support. -/
theorem complete352 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000012010001600600240140000008140140008010)
    (hweight : bitCount 180 (outsideMask word 0x1000012010001600600240140000008140140008010) ≤ 1) :
    outsideMask word 0x1000012010001600600240140000008140140008010 ∈ allowed352 := by
  exact outside_mem_of_search 8 180 11 rows352 lambdas352 0x4 0x1000012010001600600240140000008140140008010 rhs352 1
    topEColumns topETransposeColumns tree352 allowed352 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked352 checked352
    hw (he.trans rhsChecked352) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 353. -/
noncomputable def lambdas353 : Nat := 0x2000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000800000020000022000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000208000000000000000800000020000010000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 353. -/
noncomputable def rhs353 : Nat := 0x1b00000900092424092d00001b480036b40000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked353 : reconX topRColumns 0x1000012010001601400040140040008140140008020 = rhs353 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 353. -/
theorem initialChecked353 : checkSearchInitial 8 180 13 rows353 lambdas353 0x9 0x1000012010001601400040140040008140140008020 rhs353 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 353 has a listed outside support. -/
theorem complete353 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000012010001601400040140040008140140008020)
    (hweight : bitCount 180 (outsideMask word 0x1000012010001601400040140040008140140008020) ≤ 1) :
    outsideMask word 0x1000012010001601400040140040008140140008020 ∈ allowed353 := by
  exact outside_mem_of_search 8 180 13 rows353 lambdas353 0x9 0x1000012010001601400040140040008140140008020 rhs353 1
    topEColumns topETransposeColumns tree353 allowed353 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked353 checked353
    hw (he.trans rhsChecked353) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 354. -/
noncomputable def lambdas354 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000080000080400000000000000000000000000000000000000000000000000000400000010000038080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 354. -/
noncomputable def rhs354 : Nat := 0x3600000000000024001b6c0024fc0000da4000d92

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked354 : reconX topRColumns 0x1000020800006400c002400000000080d8018014004 = rhs354 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 354. -/
theorem initialChecked354 : checkSearchInitial 8 180 16 rows354 lambdas354 0x40 0x1000020800006400c002400000000080d8018014004 rhs354 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 354 has a listed outside support. -/
theorem complete354 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000020800006400c002400000000080d8018014004)
    (hweight : bitCount 180 (outsideMask word 0x1000020800006400c002400000000080d8018014004) ≤ 1) :
    outsideMask word 0x1000020800006400c002400000000080d8018014004 ∈ allowed354 := by
  exact outside_mem_of_search 8 180 16 rows354 lambdas354 0x40 0x1000020800006400c002400000000080d8018014004 rhs354 1
    topEColumns topETransposeColumns tree354 allowed354 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked354 checked354
    hw (he.trans rhsChecked354) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 355. -/
noncomputable def lambdas355 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000180000080000002000000000000000001000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 355. -/
noncomputable def rhs355 : Nat := 0x3600000900000024001b00003f9000360000004b6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked355 : reconX topRColumns 0x1000024020002c01e000400000400080c00c0010010 = rhs355 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 355. -/
theorem initialChecked355 : checkSearchInitial 8 180 15 rows355 lambdas355 0x10 0x1000024020002c01e000400000400080c00c0010010 rhs355 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 355 has a listed outside support. -/
theorem complete355 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000024020002c01e000400000400080c00c0010010)
    (hweight : bitCount 180 (outsideMask word 0x1000024020002c01e000400000400080c00c0010010) ≤ 1) :
    outsideMask word 0x1000024020002c01e000400000400080c00c0010010 ∈ allowed355 := by
  exact outside_mem_of_search 8 180 15 rows355 lambdas355 0x10 0x1000024020002c01e000400000400080c00c0010010 rhs355 1
    topEColumns topETransposeColumns tree355 allowed355 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked355 checked355
    hw (he.trans rhsChecked355) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 356. -/
noncomputable def lambdas356 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000043000000000000000000000000000000804000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000010000018000000200000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 356. -/
noncomputable def rhs356 : Nat := 0x3600001200000024001b00003f9000244800006f6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked356 : reconX topRColumns 0x1000024020002c028006400000800080c00c0010008 = rhs356 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 356. -/
theorem initialChecked356 : checkSearchInitial 8 180 14 rows356 lambdas356 0x1 0x1000024020002c028006400000800080c00c0010008 rhs356 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 356 has a listed outside support. -/
theorem complete356 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000024020002c028006400000800080c00c0010008)
    (hweight : bitCount 180 (outsideMask word 0x1000024020002c028006400000800080c00c0010008) ≤ 1) :
    outsideMask word 0x1000024020002c028006400000800080c00c0010008 ∈ allowed356 := by
  exact outside_mem_of_search 8 180 14 rows356 lambdas356 0x1 0x1000024020002c028006400000800080c00c0010008 rhs356 1
    topEColumns topETransposeColumns tree356 allowed356 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked356 checked356
    hw (he.trans rhsChecked356) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 357. -/
noncomputable def lambdas357 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000001800000800000020000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 357. -/
noncomputable def rhs357 : Nat := 0x1200000900000024001b00003f9000366c00004b6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked357 : reconX topRColumns 0x10000240200064016000401000400080c00c0008010 = rhs357 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 357. -/
theorem initialChecked357 : checkSearchInitial 8 180 13 rows357 lambdas357 0x4 0x10000240200064016000401000400080c00c0008010 rhs357 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 357 has a listed outside support. -/
theorem complete357 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10000240200064016000401000400080c00c0008010)
    (hweight : bitCount 180 (outsideMask word 0x10000240200064016000401000400080c00c0008010) ≤ 1) :
    outsideMask word 0x10000240200064016000401000400080c00c0008010 ∈ allowed357 := by
  exact outside_mem_of_search 8 180 13 rows357 lambdas357 0x4 0x10000240200064016000401000400080c00c0008010 rhs357 1
    topEColumns topETransposeColumns tree357 allowed357 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked357 checked357
    hw (he.trans rhsChecked357) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 358. -/
noncomputable def lambdas358 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000a00000020000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 358. -/
noncomputable def rhs358 : Nat := 0x36000000000924240936000036900000900000036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked358 : reconX topRColumns 0x1000036030000c00c00240000000008180180000030 = rhs358 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 358. -/
theorem initialChecked358 : checkSearchInitial 8 180 13 rows358 lambdas358 0x8 0x1000036030000c00c00240000000008180180000030 rhs358 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 358 has a listed outside support. -/
theorem complete358 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000036030000c00c00240000000008180180000030)
    (hweight : bitCount 180 (outsideMask word 0x1000036030000c00c00240000000008180180000030) ≤ 1) :
    outsideMask word 0x1000036030000c00c00240000000008180180000030 ∈ allowed358 := by
  exact outside_mem_of_search 8 180 13 rows358 lambdas358 0x8 0x1000036030000c00c00240000000008180180000030 rhs358 1
    topEColumns topETransposeColumns tree358 allowed358 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked358 checked358
    hw (he.trans rhsChecked358) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 359. -/
noncomputable def lambdas359 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000a000000200000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000003000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 359. -/
noncomputable def rhs359 : Nat := 0x36000009000924240936000036900036480000036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked359 : reconX topRColumns 0x1000036030000c01e00040000040008180180000000 = rhs359 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 359. -/
theorem initialChecked359 : checkSearchInitial 8 180 14 rows359 lambdas359 0x10 0x1000036030000c01e00040000040008180180000000 rhs359 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 359 has a listed outside support. -/
theorem complete359 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000036030000c01e00040000040008180180000000)
    (hweight : bitCount 180 (outsideMask word 0x1000036030000c01e00040000040008180180000000) ≤ 1) :
    outsideMask word 0x1000036030000c01e00040000040008180180000000 ∈ allowed359 := by
  exact outside_mem_of_search 8 180 14 rows359 lambdas359 0x10 0x1000036030000c01e00040000040008180180000000 rhs359 1
    topEColumns topETransposeColumns tree359 allowed359 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked359 checked359
    hw (he.trans rhsChecked359) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 360. -/
noncomputable def lambdas360 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 360. -/
noncomputable def rhs360 : Nat := 0x3f000000024900240240000012480012480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked360 : reconX topRColumns 0x1000090010007e00e00240040000008a00000080000 = rhs360 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 360. -/
theorem initialChecked360 : checkSearchInitial 8 180 11 rows360 lambdas360 0x10 0x1000090010007e00e00240040000008a00000080000 rhs360 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 360 has a listed outside support. -/
theorem complete360 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000090010007e00e00240040000008a00000080000)
    (hweight : bitCount 180 (outsideMask word 0x1000090010007e00e00240040000008a00000080000) ≤ 1) :
    outsideMask word 0x1000090010007e00e00240040000008a00000080000 ∈ allowed360 := by
  exact outside_mem_of_search 8 180 11 rows360 lambdas360 0x10 0x1000090010007e00e00240040000008a00000080000 rhs360 1
    topEColumns topETransposeColumns tree360 allowed360 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked360 checked360
    hw (he.trans rhsChecked360) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 361. -/
noncomputable def lambdas361 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 361. -/
noncomputable def rhs361 : Nat := 0x3f0000000000002406c0000012480024480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked361 : reconX topRColumns 0x1000120020007e00e00240040000008600000100000 = rhs361 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 361. -/
theorem initialChecked361 : checkSearchInitial 8 180 11 rows361 lambdas361 0x10 0x1000120020007e00e00240040000008600000100000 rhs361 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 361 has a listed outside support. -/
theorem complete361 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000120020007e00e00240040000008600000100000)
    (hweight : bitCount 180 (outsideMask word 0x1000120020007e00e00240040000008600000100000) ≤ 1) :
    outsideMask word 0x1000120020007e00e00240040000008600000100000 ∈ allowed361 := by
  exact outside_mem_of_search 8 180 11 rows361 lambdas361 0x10 0x1000120020007e00e00240040000008600000100000 rhs361 1
    topEColumns topETransposeColumns tree361 allowed361 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked361 checked361
    hw (he.trans rhsChecked361) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 362. -/
noncomputable def lambdas362 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000200000201000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000200000008000002000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000001800000020000020800000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 362. -/
noncomputable def rhs362 : Nat := 0xd800369000006c90000090000090009240004add8003f

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked362 : reconX topRColumns 0x10002000000004806080b0020029001001000005003 = rhs362 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 362. -/
theorem initialChecked362 : checkSearchInitial 8 180 14 rows362 lambdas362 0x5 0x10002000000004806080b0020029001001000005003 rhs362 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 362 has a listed outside support. -/
theorem complete362 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10002000000004806080b0020029001001000005003)
    (hweight : bitCount 180 (outsideMask word 0x10002000000004806080b0020029001001000005003) ≤ 1) :
    outsideMask word 0x10002000000004806080b0020029001001000005003 ∈ allowed362 := by
  exact outside_mem_of_search 8 180 14 rows362 lambdas362 0x5 0x10002000000004806080b0020029001001000005003 rhs362 1
    topEColumns topETransposeColumns tree362 allowed362 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked362 checked362
    hw (he.trans rhsChecked362) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 363. -/
noncomputable def lambdas363 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000200000201000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000040000000000000000000000000000002000002088000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 363. -/
noncomputable def rhs363 : Nat := 0xd80036900000fc90000090000090009240004add80024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked363 : reconX topRColumns 0x1000200000000480f081b0020009001001000005000 = rhs363 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 363. -/
theorem initialChecked363 : checkSearchInitial 8 180 14 rows363 lambdas363 0x4 0x1000200000000480f081b0020009001001000005000 rhs363 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 363 has a listed outside support. -/
theorem complete363 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000200000000480f081b0020009001001000005000)
    (hweight : bitCount 180 (outsideMask word 0x1000200000000480f081b0020009001001000005000) ≤ 1) :
    outsideMask word 0x1000200000000480f081b0020009001001000005000 ∈ allowed363 := by
  exact outside_mem_of_search 8 180 14 rows363 lambdas363 0x4 0x1000200000000480f081b0020009001001000005000 rhs363 1
    topEColumns topETransposeColumns tree363 allowed363 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked363 checked363
    hw (he.trans rhsChecked363) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 364. -/
noncomputable def lambdas364 : Nat := 0x200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000004000000000000000000000000000000300000020000000000000000000000000600000208000000000000000000000020000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 364. -/
noncomputable def rhs364 : Nat := 0xd80036b4000000900000900000900049200003fd80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked364 : reconX topRColumns 0x10002000000006c0088070028031001001000003000 = rhs364 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 364. -/
theorem initialChecked364 : checkSearchInitial 8 180 12 rows364 lambdas364 0x3 0x10002000000006c0088070028031001001000003000 rhs364 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 364 has a listed outside support. -/
theorem complete364 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10002000000006c0088070028031001001000003000)
    (hweight : bitCount 180 (outsideMask word 0x10002000000006c0088070028031001001000003000) ≤ 1) :
    outsideMask word 0x10002000000006c0088070028031001001000003000 ∈ allowed364 := by
  exact outside_mem_of_search 8 180 12 rows364 lambdas364 0x3 0x10002000000006c0088070028031001001000003000 rhs364 1
    topEColumns topETransposeColumns tree364 allowed364 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked364 checked364
    hw (he.trans rhsChecked364) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 365. -/
noncomputable def lambdas365 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000180000002000002080000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000c00000000000000000000000000000001 (Nat.shiftLeft 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000200000201000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 365. -/
noncomputable def rhs365 : Nat := 0xd80036480000fc90000090000090000000004bfd80024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked365 : reconX topRColumns 0x1000200000000900e881b0010009001001000003000 = rhs365 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 365. -/
theorem initialChecked365 : checkSearchInitial 8 180 20 rows365 lambdas365 0x10 0x1000200000000900e881b0010009001001000003000 rhs365 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 365 has a listed outside support. -/
theorem complete365 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000200000000900e881b0010009001001000003000)
    (hweight : bitCount 180 (outsideMask word 0x1000200000000900e881b0010009001001000003000) ≤ 1) :
    outsideMask word 0x1000200000000900e881b0010009001001000003000 ∈ allowed365 := by
  exact outside_mem_of_search 8 180 20 rows365 lambdas365 0x10 0x1000200000000900e881b0010009001001000003000 rhs365 1
    topEColumns topETransposeColumns tree365 allowed365 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked365 checked365
    hw (he.trans rhsChecked365) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 366. -/
noncomputable def lambdas366 : Nat := (Nat.lor 0x1000000000000000000000000000000000000000000000000000000000020000020100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000018000000200000208000000000000000100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040 (Nat.shiftLeft 0x800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 366. -/
noncomputable def rhs366 : Nat := 0xd80036000000fc90000090000090009240004b6d80024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked366 : reconX topRColumns 0x1000200000000d80e081b0000009001001000006000 = rhs366 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 366. -/
theorem initialChecked366 : checkSearchInitial 8 180 18 rows366 lambdas366 0x8 0x1000200000000d80e081b0000009001001000006000 rhs366 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 366 has a listed outside support. -/
theorem complete366 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000200000000d80e081b0000009001001000006000)
    (hweight : bitCount 180 (outsideMask word 0x1000200000000d80e081b0000009001001000006000) ≤ 1) :
    outsideMask word 0x1000200000000d80e081b0000009001001000006000 ∈ allowed366 := by
  exact outside_mem_of_search 8 180 18 rows366 lambdas366 0x8 0x1000200000000d80e081b0000009001001000006000 rhs366 1
    topEColumns topETransposeColumns tree366 allowed366 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked366 checked366
    hw (he.trans rhsChecked366) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 367. -/
noncomputable def lambdas367 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000a0000020800000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000c00000000000022

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 367. -/
noncomputable def rhs367 : Nat := 0xd80036240000009000009000009000492000024d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked367 : reconX topRColumns 0x1000200000000fc0188070008031001001000000000 = rhs367 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 367. -/
theorem initialChecked367 : checkSearchInitial 8 180 11 rows367 lambdas367 0x21 0x1000200000000fc0188070008031001001000000000 rhs367 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 367 has a listed outside support. -/
theorem complete367 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000200000000fc0188070008031001001000000000)
    (hweight : bitCount 180 (outsideMask word 0x1000200000000fc0188070008031001001000000000) ≤ 1) :
    outsideMask word 0x1000200000000fc0188070008031001001000000000 ∈ allowed367 := by
  exact outside_mem_of_search 8 180 11 rows367 lambdas367 0x21 0x1000200000000fc0188070008031001001000000000 rhs367 1
    topEColumns topETransposeColumns tree367 allowed367 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked367 checked367
    hw (he.trans rhsChecked367) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 368. -/
noncomputable def lambdas368 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 368. -/
noncomputable def rhs368 : Nat := 0x3f000000924000249000000012480480480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked368 : reconX topRColumns 0x1000480080007e00e0024004000000d000000400000 = rhs368 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 368. -/
theorem initialChecked368 : checkSearchInitial 8 180 11 rows368 lambdas368 0x10 0x1000480080007e00e0024004000000d000000400000 rhs368 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 368 has a listed outside support. -/
theorem complete368 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000480080007e00e0024004000000d000000400000)
    (hweight : bitCount 180 (outsideMask word 0x1000480080007e00e0024004000000d000000400000) ≤ 1) :
    outsideMask word 0x1000480080007e00e0024004000000d000000400000 ∈ allowed368 := by
  exact outside_mem_of_search 8 180 11 rows368 lambdas368 0x10 0x1000480080007e00e0024004000000d000000400000 rhs368 1
    topEColumns topETransposeColumns tree368 allowed368 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked368 checked368
    hw (he.trans rhsChecked368) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 369. -/
noncomputable def lambdas369 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 369. -/
noncomputable def rhs369 : Nat := 0x3f00000000000025b000000012480900480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked369 : reconX topRColumns 0x1000900100007e00e0024004000000b000000800000 = rhs369 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 369. -/
theorem initialChecked369 : checkSearchInitial 8 180 11 rows369 lambdas369 0x10 0x1000900100007e00e0024004000000b000000800000 rhs369 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 369 has a listed outside support. -/
theorem complete369 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1000900100007e00e0024004000000b000000800000)
    (hweight : bitCount 180 (outsideMask word 0x1000900100007e00e0024004000000b000000800000) ≤ 1) :
    outsideMask word 0x1000900100007e00e0024004000000b000000800000 ∈ allowed369 := by
  exact outside_mem_of_search 8 180 11 rows369 lambdas369 0x10 0x1000900100007e00e0024004000000b000000800000 rhs369 1
    topEColumns topETransposeColumns tree369 allowed369 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked369 checked369
    hw (he.trans rhsChecked369) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 370. -/
noncomputable def lambdas370 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000020000020000000200000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000002080000000000000000000000000000100800000000000000000000000000000800000030000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 370. -/
noncomputable def rhs370 : Nat := 0xdb600001b480009000000240000000012da4036fc9

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked370 : reconX topRColumns 0x1001000000000003281480c0015004000800000001d = rhs370 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 370. -/
theorem initialChecked370 : checkSearchInitial 8 180 11 rows370 lambdas370 0x1 0x1001000000000003281480c0015004000800000001d rhs370 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 370 has a listed outside support. -/
theorem complete370 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001000000000003281480c0015004000800000001d)
    (hweight : bitCount 180 (outsideMask word 0x1001000000000003281480c0015004000800000001d) ≤ 1) :
    outsideMask word 0x1001000000000003281480c0015004000800000001d ∈ allowed370 := by
  exact outside_mem_of_search 8 180 11 rows370 lambdas370 0x1 0x1001000000000003281480c0015004000800000001d rhs370 1
    topEColumns topETransposeColumns tree370 allowed370 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked370 checked370
    hw (he.trans rhsChecked370) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 371. -/
noncomputable def lambdas371 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000020000020000000200000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000006000002080000000000000000000000200000020000000000000000000000000800000030000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 371. -/
noncomputable def rhs371 : Nat := 0xdb600001b240009000000240000000012936036fc0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked371 : reconX topRColumns 0x1001000000000003441440c0014804000800000001e = rhs371 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 371. -/
theorem initialChecked371 : checkSearchInitial 8 180 11 rows371 lambdas371 0x3 0x1001000000000003441440c0014804000800000001e rhs371 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 371 has a listed outside support. -/
theorem complete371 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001000000000003441440c0014804000800000001e)
    (hweight : bitCount 180 (outsideMask word 0x1001000000000003441440c0014804000800000001e) ≤ 1) :
    outsideMask word 0x1001000000000003441440c0014804000800000001e ∈ allowed371 := by
  exact outside_mem_of_search 8 180 11 rows371 lambdas371 0x3 0x1001000000000003441440c0014804000800000001e rhs371 1
    topEColumns topETransposeColumns tree371 allowed371 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked371 checked371
    hw (he.trans rhsChecked371) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 372. -/
noncomputable def lambdas372 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000a0000020800000000000000000000001000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 372. -/
noncomputable def rhs372 : Nat := 0xdb600003f90000900000024000000001248003691b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked372 : reconX topRColumns 0x1001000000000007701d00c00060040008000000003 = rhs372 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 372. -/
theorem initialChecked372 : checkSearchInitial 8 180 12 rows372 lambdas372 0x8 0x1001000000000007701d00c00060040008000000003 rhs372 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 372 has a listed outside support. -/
theorem complete372 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001000000000007701d00c00060040008000000003)
    (hweight : bitCount 180 (outsideMask word 0x1001000000000007701d00c00060040008000000003) ≤ 1) :
    outsideMask word 0x1001000000000007701d00c00060040008000000003 ∈ allowed372 := by
  exact outside_mem_of_search 8 180 12 rows372 lambdas372 0x8 0x1001000000000007701d00c00060040008000000003 rhs372 1
    topEColumns topETransposeColumns tree372 allowed372 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked372 checked372
    hw (he.trans rhsChecked372) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 373. -/
noncomputable def lambdas373 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000002800000800000820000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 373. -/
noncomputable def rhs373 : Nat := 0xdb600003f480009000000240000000012da4036909

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked373 : reconX topRColumns 0x1001000000000007a81c80c00050040008000000005 = rhs373 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 373. -/
theorem initialChecked373 : checkSearchInitial 8 180 12 rows373 lambdas373 0x8 0x1001000000000007a81c80c00050040008000000005 rhs373 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 373 has a listed outside support. -/
theorem complete373 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001000000000007a81c80c00050040008000000005)
    (hweight : bitCount 180 (outsideMask word 0x1001000000000007a81c80c00050040008000000005) ≤ 1) :
    outsideMask word 0x1001000000000007a81c80c00050040008000000005 ∈ allowed373 := by
  exact outside_mem_of_search 8 180 12 rows373 lambdas373 0x8 0x1001000000000007a81c80c00050040008000000005 rhs373 1
    topEColumns topETransposeColumns tree373 allowed373 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked373 checked373
    hw (he.trans rhsChecked373) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 374. -/
noncomputable def lambdas374 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000a0000020800000000000000000000001000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 374. -/
noncomputable def rhs374 : Nat := 0xdb600003f240009000000240000000012936036900

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked374 : reconX topRColumns 0x1001000000000007c41c40c00048040008000000006 = rhs374 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 374. -/
theorem initialChecked374 : checkSearchInitial 8 180 12 rows374 lambdas374 0x8 0x1001000000000007c41c40c00048040008000000006 rhs374 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 374 has a listed outside support. -/
theorem complete374 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001000000000007c41c40c00048040008000000006)
    (hweight : bitCount 180 (outsideMask word 0x1001000000000007c41c40c00048040008000000006) ≤ 1) :
    outsideMask word 0x1001000000000007c41c40c00048040008000000006 ∈ allowed374 := by
  exact outside_mem_of_search 8 180 12 rows374 lambdas374 0x8 0x1001000000000007c41c40c00048040008000000006 rhs374 1
    topEColumns topETransposeColumns tree374 allowed374 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked374 checked374
    hw (he.trans rhsChecked374) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 375. -/
noncomputable def lambdas375 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000030000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 375. -/
noncomputable def rhs375 : Nat := 0x3f000036d80000240000000012489000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked375 : reconX topRColumns 0x1001200200007e00e00240040000038000001000000 = rhs375 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 375. -/
theorem initialChecked375 : checkSearchInitial 8 180 11 rows375 lambdas375 0x10 0x1001200200007e00e00240040000038000001000000 rhs375 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 375 has a listed outside support. -/
theorem complete375 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001200200007e00e00240040000038000001000000)
    (hweight : bitCount 180 (outsideMask word 0x1001200200007e00e00240040000038000001000000) ≤ 1) :
    outsideMask word 0x1001200200007e00e00240040000038000001000000 ∈ allowed375 := by
  exact outside_mem_of_search 8 180 11 rows375 lambdas375 0x10 0x1001200200007e00e00240040000038000001000000 rhs375 1
    topEColumns topETransposeColumns tree375 allowed375 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked375 checked375
    hw (he.trans rhsChecked375) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 376. -/
noncomputable def lambdas376 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000c0000040000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000e00000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 376. -/
noncomputable def rhs376 : Nat := 0xb6d00001b48001248000048000001b000000024d92

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked376 : reconX topRColumns 0x10016006000000000022c0ac0140080010003000000 = rhs376 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 376. -/
theorem initialChecked376 : checkSearchInitial 8 180 10 rows376 lambdas376 0x5 0x10016006000000000022c0ac0140080010003000000 rhs376 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 376 has a listed outside support. -/
theorem complete376 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10016006000000000022c0ac0140080010003000000)
    (hweight : bitCount 180 (outsideMask word 0x10016006000000000022c0ac0140080010003000000) ≤ 1) :
    outsideMask word 0x10016006000000000022c0ac0140080010003000000 ∈ allowed376 := by
  exact outside_mem_of_search 8 180 10 rows376 lambdas376 0x5 0x10016006000000000022c0ac0140080010003000000 rhs376 1
    topEColumns topETransposeColumns tree376 allowed376 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked376 checked376
    hw (he.trans rhsChecked376) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 377. -/
noncomputable def lambdas377 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000010000030000020c4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000c0000080000000400000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000e00000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 377. -/
noncomputable def rhs377 : Nat := 0x6db00002dd80024d8000090000002d000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked377 : reconX topRColumns 0x1001a00a000000000043407400c0100020005000000 = rhs377 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 377. -/
theorem initialChecked377 : checkSearchInitial 8 180 11 rows377 lambdas377 0x81 0x1001a00a000000000043407400c0100020005000000 rhs377 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 377 has a listed outside support. -/
theorem complete377 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1001a00a000000000043407400c0100020005000000)
    (hweight : bitCount 180 (outsideMask word 0x1001a00a000000000043407400c0100020005000000) ≤ 1) :
    outsideMask word 0x1001a00a000000000043407400c0100020005000000 ∈ allowed377 := by
  exact outside_mem_of_search 8 180 11 rows377 lambdas377 0x81 0x1001a00a000000000043407400c0100020005000000 rhs377 1
    topEColumns topETransposeColumns tree377 allowed377 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked377 checked377
    hw (he.trans rhsChecked377) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 378. -/
noncomputable def lambdas378 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000020000000c000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000208000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 378. -/
noncomputable def rhs378 : Nat := 0x6db00003fd8001b4800006c0000009000000012da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked378 : reconX topRColumns 0x10022002000000000032807400c00e0018001000000 = rhs378 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 378. -/
theorem initialChecked378 : checkSearchInitial 8 180 11 rows378 lambdas378 0x80 0x10022002000000000032807400c00e0018001000000 rhs378 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 378 has a listed outside support. -/
theorem complete378 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10022002000000000032807400c00e0018001000000)
    (hweight : bitCount 180 (outsideMask word 0x10022002000000000032807400c00e0018001000000) ≤ 1) :
    outsideMask word 0x10022002000000000032807400c00e0018001000000 ∈ allowed378 := by
  exact outside_mem_of_search 8 180 11 rows378 lambdas378 0x80 0x10022002000000000032807400c00e0018001000000 rhs378 1
    topEColumns topETransposeColumns tree378 allowed378 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked378 checked378
    hw (he.trans rhsChecked378) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 379. -/
noncomputable def lambdas379 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 379. -/
noncomputable def rhs379 : Nat := 0x246c0000000000000000012000492000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked379 : reconX topRColumns 0x1002400400000000fc0380180038020000002000000 = rhs379 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 379. -/
theorem initialChecked379 : checkSearchInitial 8 180 9 rows379 lambdas379 0x8 0x1002400400000000fc0380180038020000002000000 rhs379 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 379 has a listed outside support. -/
theorem complete379 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1002400400000000fc0380180038020000002000000)
    (hweight : bitCount 180 (outsideMask word 0x1002400400000000fc0380180038020000002000000) ≤ 1) :
    outsideMask word 0x1002400400000000fc0380180038020000002000000 ∈ allowed379 := by
  exact outside_mem_of_search 8 180 9 rows379 lambdas379 0x8 0x1002400400000000fc0380180038020000002000000 rhs379 1
    topEColumns topETransposeColumns tree379 allowed379 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked379 checked379
    hw (he.trans rhsChecked379) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 380. -/
noncomputable def lambdas380 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 380. -/
noncomputable def rhs380 : Nat := 0x1b900000000000000000012012480000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked380 : reconX topRColumns 0x1002400400000007e00c401801c0020000002000000 = rhs380 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 380. -/
theorem initialChecked380 : checkSearchInitial 8 180 10 rows380 lambdas380 0x8 0x1002400400000007e00c401801c0020000002000000 rhs380 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 380 has a listed outside support. -/
theorem complete380 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1002400400000007e00c401801c0020000002000000)
    (hweight : bitCount 180 (outsideMask word 0x1002400400000007e00c401801c0020000002000000) ≤ 1) :
    outsideMask word 0x1002400400000007e00c401801c0020000002000000 ∈ allowed380 := by
  exact outside_mem_of_search 8 180 10 rows380 lambdas380 0x8 0x1002400400000007e00c401801c0020000002000000 rhs380 1
    topEColumns topETransposeColumns tree380 allowed380 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked380 checked380
    hw (he.trans rhsChecked380) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 381. -/
noncomputable def lambdas381 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000820000000000000000000000000000040200000000000000000000000000000300000004000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 381. -/
noncomputable def rhs381 : Nat := 0x12000024fc00000000000000249120006d2000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked381 : reconX topRColumns 0x10024004000024002c0280100018020000002028003 = rhs381 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 381. -/
theorem initialChecked381 : checkSearchInitial 8 180 12 rows381 lambdas381 0x3 0x10024004000024002c0280100018020000002028003 rhs381 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 381 has a listed outside support. -/
theorem complete381 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10024004000024002c0280100018020000002028003)
    (hweight : bitCount 180 (outsideMask word 0x10024004000024002c0280100018020000002028003) ≤ 1) :
    outsideMask word 0x10024004000024002c0280100018020000002028003 ∈ allowed381 := by
  exact outside_mem_of_search 8 180 12 rows381 lambdas381 0x3 0x10024004000024002c0280100018020000002028003 rhs381 1
    topEColumns topETransposeColumns tree381 allowed381 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked381 checked381
    hw (he.trans rhsChecked381) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 382. -/
noncomputable def lambdas382 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000002000000080000040000000200000000000000000000000000000000002080000000000000000000000000000100800000000000000000000000000000030000010000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 382. -/
noncomputable def rhs382 : Nat := 0x1200003f9000000000000000249120126c0000ff6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked382 : reconX topRColumns 0x10024004000024032004401000c0020000002028018 = rhs382 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 382. -/
theorem initialChecked382 : checkSearchInitial 8 180 11 rows382 lambdas382 0x1 0x10024004000024032004401000c0020000002028018 rhs382 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 382 has a listed outside support. -/
theorem complete382 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10024004000024032004401000c0020000002028018)
    (hweight : bitCount 180 (outsideMask word 0x10024004000024032004401000c0020000002028018) ≤ 1) :
    outsideMask word 0x10024004000024032004401000c0020000002028018 ∈ allowed382 := by
  exact outside_mem_of_search 8 180 11 rows382 lambdas382 0x1 0x10024004000024032004401000c0020000002028018 rhs382 1
    topEColumns topETransposeColumns tree382 allowed382 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked382 checked382
    hw (he.trans rhsChecked382) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 383. -/
noncomputable def lambdas383 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000020800000000000402000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000300000004000000800000000000000000000000208000000000000000000000010000010400000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 383. -/
noncomputable def rhs383 : Nat := 0x1b00002d900000000000000012492036fc0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked383 : reconX topRColumns 0x1002400400003601400040140040020000002018030 = rhs383 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 383. -/
theorem initialChecked383 : checkSearchInitial 8 180 10 rows383 lambdas383 0x2 0x1002400400003601400040140040020000002018030 rhs383 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 383 has a listed outside support. -/
theorem complete383 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1002400400003601400040140040020000002018030)
    (hweight : bitCount 180 (outsideMask word 0x1002400400003601400040140040020000002018030) ≤ 1) :
    outsideMask word 0x1002400400003601400040140040020000002018030 ∈ allowed383 := by
  exact outside_mem_of_search 8 180 10 rows383 lambdas383 0x2 0x1002400400003601400040140040020000002018030 rhs383 1
    topEColumns topETransposeColumns tree383 allowed383 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked383 checked383
    hw (he.trans rhsChecked383) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 384. -/
noncomputable def lambdas384 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000208000000000000000000000010000020000000840

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 384. -/
noncomputable def rhs384 : Nat := 0x3f00002d900000000000000012492036900000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked384 : reconX topRColumns 0x1002400400007e01c00040040040020000002000030 = rhs384 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 384. -/
theorem initialChecked384 : checkSearchInitial 8 180 12 rows384 lambdas384 0x20 0x1002400400007e01c00040040040020000002000030 rhs384 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 384 has a listed outside support. -/
theorem complete384 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1002400400007e01c00040040040020000002000030)
    (hweight : bitCount 180 (outsideMask word 0x1002400400007e01c00040040040020000002000030) ≤ 1) :
    outsideMask word 0x1002400400007e01c00040040040020000002000030 ∈ allowed384 := by
  exact outside_mem_of_search 8 180 12 rows384 lambdas384 0x20 0x1002400400007e01c00040040040020000002000030 rhs384 1
    topEColumns topETransposeColumns tree384 allowed384 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked384 checked384
    hw (he.trans rhsChecked384) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 385. -/
noncomputable def lambdas385 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000001000001000001044000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000043000002800002080000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000600000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 385. -/
noncomputable def rhs385 : Nat := 0xdb6000012000036900000d80000024000000024d92

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked385 : reconX topRColumns 0x10028008000000000063c0c001801a0030004000000 = rhs385 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 385. -/
theorem initialChecked385 : checkSearchInitial 8 180 16 rows385 lambdas385 0x800 0x10028008000000000063c0c001801a0030004000000 rhs385 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 385 has a listed outside support. -/
theorem complete385 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10028008000000000063c0c001801a0030004000000)
    (hweight : bitCount 180 (outsideMask word 0x10028008000000000063c0c001801a0030004000000) ≤ 1) :
    outsideMask word 0x10028008000000000063c0c001801a0030004000000 ∈ allowed385 := by
  exact outside_mem_of_search 8 180 16 rows385 lambdas385 0x800 0x10028008000000000063c0c001801a0030004000000 rhs385 1
    topEColumns topETransposeColumns tree385 allowed385 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked385 checked385
    hw (he.trans rhsChecked385) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 386. -/
noncomputable def lambdas386 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 386. -/
noncomputable def rhs386 : Nat := 0x24d92000012000000000012fc0000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked386 : reconX topRColumns 0x1002bc05c0000000000240180000020000002e00000 = rhs386 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 386. -/
theorem initialChecked386 : checkSearchInitial 8 180 8 rows386 lambdas386 0x28 0x1002bc05c0000000000240180000020000002e00000 rhs386 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 386 has a listed outside support. -/
theorem complete386 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1002bc05c0000000000240180000020000002e00000)
    (hweight : bitCount 180 (outsideMask word 0x1002bc05c0000000000240180000020000002e00000) ≤ 1) :
    outsideMask word 0x1002bc05c0000000000240180000020000002e00000 ∈ allowed386 := by
  exact outside_mem_of_search 8 180 8 rows386 lambdas386 0x28 0x1002bc05c0000000000240180000020000002e00000 rhs386 1
    topEColumns topETransposeColumns tree386 allowed386 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked386 checked386
    hw (he.trans rhsChecked386) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 387. -/
noncomputable def lambdas387 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000020000020100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000100000180000000400000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000004000008100000200000008000000000000000020000000000000000000000000030200018200000000000000000000000820000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 387. -/
noncomputable def rhs387 : Nat := 0x6db000012240024b40000900000000036036000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked387 : reconX topRColumns 0x1004000000000001044100740088128020000000036 = rhs387 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 387. -/
theorem initialChecked387 : checkSearchInitial 8 180 13 rows387 lambdas387 0x81 0x1004000000000001044100740088128020000000036 rhs387 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 387 has a listed outside support. -/
theorem complete387 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1004000000000001044100740088128020000000036)
    (hweight : bitCount 180 (outsideMask word 0x1004000000000001044100740088128020000000036) ≤ 1) :
    outsideMask word 0x1004000000000001044100740088128020000000036 ∈ allowed387 := by
  exact outside_mem_of_search 8 180 13 rows387 lambdas387 0x81 0x1004000000000001044100740088128020000000036 rhs387 1
    topEColumns topETransposeColumns tree387 allowed387 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked387 checked387
    hw (he.trans rhsChecked387) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 388. -/
noncomputable def lambdas388 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000200000201000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000200000180000002000000000000000000000001000000000000000000000000400000000000000000000000000000030000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 388. -/
noncomputable def rhs388 : Nat := 0x6db000000000024b40000900000000012480000ff6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked388 : reconX topRColumns 0x1004000000000003604540740000128020000000018 = rhs388 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 388. -/
theorem initialChecked388 : checkSearchInitial 8 180 10 rows388 lambdas388 0x1 0x1004000000000003604540740000128020000000018 rhs388 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 388 has a listed outside support. -/
theorem complete388 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1004000000000003604540740000128020000000018)
    (hweight : bitCount 180 (outsideMask word 0x1004000000000003604540740000128020000000018) ≤ 1) :
    outsideMask word 0x1004000000000003604540740000128020000000018 ∈ allowed388 := by
  exact outside_mem_of_search 8 180 10 rows388 lambdas388 0x1 0x1004000000000003604540740000128020000000018 rhs388 1
    topEColumns topETransposeColumns tree388 allowed388 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked388 checked388
    hw (he.trans rhsChecked388) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 389. -/
noncomputable def lambdas389 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 389. -/
noncomputable def rhs389 : Nat := 0x492000492000000000024fc0000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked389 : reconX topRColumns 0x10047c09c0000000000240180000010000004e00000 = rhs389 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 389. -/
theorem initialChecked389 : checkSearchInitial 8 180 8 rows389 lambdas389 0x28 0x10047c09c0000000000240180000010000004e00000 rhs389 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 389 has a listed outside support. -/
theorem complete389 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10047c09c0000000000240180000010000004e00000)
    (hweight : bitCount 180 (outsideMask word 0x10047c09c0000000000240180000010000004e00000) ≤ 1) :
    outsideMask word 0x10047c09c0000000000240180000010000004e00000 ∈ allowed389 := by
  exact outside_mem_of_search 8 180 8 rows389 lambdas389 0x28 0x10047c09c0000000000240180000010000004e00000 rhs389 1
    topEColumns topETransposeColumns tree389 allowed389 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked389 checked389
    hw (he.trans rhsChecked389) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 390. -/
noncomputable def lambdas390 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 390. -/
noncomputable def rhs390 : Nat := 0xfc0000480000000000024000492000da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked390 : reconX topRColumns 0x1004800800000000fc0380180038010000004000000 = rhs390 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 390. -/
theorem initialChecked390 : checkSearchInitial 8 180 9 rows390 lambdas390 0x8 0x1004800800000000fc0380180038010000004000000 rhs390 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 390 has a listed outside support. -/
theorem complete390 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1004800800000000fc0380180038010000004000000)
    (hweight : bitCount 180 (outsideMask word 0x1004800800000000fc0380180038010000004000000) ≤ 1) :
    outsideMask word 0x1004800800000000fc0380180038010000004000000 ∈ allowed390 := by
  exact outside_mem_of_search 8 180 9 rows390 lambdas390 0x8 0x1004800800000000fc0380180038010000004000000 rhs390 1
    topEColumns topETransposeColumns tree390 allowed390 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked390 checked390
    hw (he.trans rhsChecked390) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 391. -/
noncomputable def lambdas391 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 391. -/
noncomputable def rhs391 : Nat := 0x3f000000480000000000024012480000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked391 : reconX topRColumns 0x1004800800000007e00c401801c0010000004000000 = rhs391 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 391. -/
theorem initialChecked391 : checkSearchInitial 8 180 10 rows391 lambdas391 0x8 0x1004800800000007e00c401801c0010000004000000 rhs391 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 391 has a listed outside support. -/
theorem complete391 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1004800800000007e00c401801c0010000004000000)
    (hweight : bitCount 180 (outsideMask word 0x1004800800000007e00c401801c0010000004000000) ≤ 1) :
    outsideMask word 0x1004800800000007e00c401801c0010000004000000 ∈ allowed391 := by
  exact outside_mem_of_search 8 180 10 rows391 lambdas391 0x8 0x1004800800000007e00c401801c0010000004000000 rhs391 1
    topEColumns topETransposeColumns tree391 allowed391 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked391 checked391
    hw (he.trans rhsChecked391) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 392. -/
noncomputable def lambdas392 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000288400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000082000000000000000000000000000004020000000000000000000000000000000000000000000000000000000800000c00000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 392. -/
noncomputable def rhs392 : Nat := 0x120000006c00004800000000249240006d2000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked392 : reconX topRColumns 0x10048008000024002c0280100018010000004028003 = rhs392 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 392. -/
theorem initialChecked392 : checkSearchInitial 8 180 11 rows392 lambdas392 0x1 0x10048008000024002c0280100018010000004028003 rhs392 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 392 has a listed outside support. -/
theorem complete392 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10048008000024002c0280100018010000004028003)
    (hweight : bitCount 180 (outsideMask word 0x10048008000024002c0280100018010000004028003) ≤ 1) :
    outsideMask word 0x10048008000024002c0280100018010000004028003 ∈ allowed392 := by
  exact outside_mem_of_search 8 180 11 rows392 lambdas392 0x1 0x10048008000024002c0280100018010000004028003 rhs392 1
    topEColumns topETransposeColumns tree392 allowed392 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked392 checked392
    hw (he.trans rhsChecked392) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 393. -/
noncomputable def lambdas393 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000040000040000002000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000003000001040000000000082000000000000000010000000000000000000000000200000006000006000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001 (Nat.shiftLeft 0x100000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 393. -/
noncomputable def rhs393 : Nat := 0x1200001b0000004800000000249240126c0000ff6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked393 : reconX topRColumns 0x10048008000024032004401000c0010000004028018 = rhs393 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 393. -/
theorem initialChecked393 : checkSearchInitial 8 180 20 rows393 lambdas393 0x4 0x10048008000024032004401000c0010000004028018 rhs393 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 393 has a listed outside support. -/
theorem complete393 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x10048008000024032004401000c0010000004028018)
    (hweight : bitCount 180 (outsideMask word 0x10048008000024032004401000c0010000004028018) ≤ 1) :
    outsideMask word 0x10048008000024032004401000c0010000004028018 ∈ allowed393 := by
  exact outside_mem_of_search 8 180 20 rows393 lambdas393 0x4 0x10048008000024032004401000c0010000004028018 rhs393 1
    topEColumns topETransposeColumns tree393 allowed393 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked393 checked393
    hw (he.trans rhsChecked393) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 394. -/
noncomputable def lambdas394 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000300000004000000800000000000000000000000208000000000000000000000010000010400000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 394. -/
noncomputable def rhs394 : Nat := 0x1b0000090000004800000000124a4036fc0000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked394 : reconX topRColumns 0x1004800800003601400040140040010000004018030 = rhs394 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 394. -/
theorem initialChecked394 : checkSearchInitial 8 180 10 rows394 lambdas394 0x2 0x1004800800003601400040140040010000004018030 rhs394 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 394 has a listed outside support. -/
theorem complete394 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1004800800003601400040140040010000004018030)
    (hweight : bitCount 180 (outsideMask word 0x1004800800003601400040140040010000004018030) ≤ 1) :
    outsideMask word 0x1004800800003601400040140040010000004018030 ∈ allowed394 := by
  exact outside_mem_of_search 8 180 10 rows394 lambdas394 0x2 0x1004800800003601400040140040010000004018030 rhs394 1
    topEColumns topETransposeColumns tree394 allowed394 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked394 checked394
    hw (he.trans rhsChecked394) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 395. -/
noncomputable def lambdas395 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000208000000000000000000000010000020000000840

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 395. -/
noncomputable def rhs395 : Nat := 0x3f0000090000004800000000124a4036900000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked395 : reconX topRColumns 0x1004800800007e01c00040040040010000004000030 = rhs395 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 395. -/
theorem initialChecked395 : checkSearchInitial 8 180 12 rows395 lambdas395 0x20 0x1004800800007e01c00040040040010000004000030 rhs395 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 395 has a listed outside support. -/
theorem complete395 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1004800800007e01c00040040040010000004000030)
    (hweight : bitCount 180 (outsideMask word 0x1004800800007e01c00040040040010000004000030) ≤ 1) :
    outsideMask word 0x1004800800007e01c00040040040010000004000030 ∈ allowed395 := by
  exact outside_mem_of_search 8 180 12 rows395 lambdas395 0x20 0x1004800800007e01c00040040040010000004000030 rhs395 1
    topEColumns topETransposeColumns tree395 allowed395 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked395 checked395
    hw (he.trans rhsChecked395) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 396. -/
noncomputable def lambdas396 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000018000008000000040000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000208000000000000000000000000000020800000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 396. -/
noncomputable def rhs396 : Nat := 0xb6d00001200002d900000b40000000036d80036d80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked396 : reconX topRColumns 0x1005000000000001205100ac0100160028000000030 = rhs396 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 396. -/
theorem initialChecked396 : checkSearchInitial 8 180 14 rows396 lambdas396 0x40 0x1005000000000001205100ac0100160028000000030 rhs396 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 396 has a listed outside support. -/
theorem complete396 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1005000000000001205100ac0100160028000000030)
    (hweight : bitCount 180 (outsideMask word 0x1005000000000001205100ac0100160028000000030) ≤ 1) :
    outsideMask word 0x1005000000000001205100ac0100160028000000030 ∈ allowed396 := by
  exact outside_mem_of_search 8 180 14 rows396 lambdas396 0x40 0x1005000000000001205100ac0100160028000000030 rhs396 1
    topEColumns topETransposeColumns tree396 allowed396 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked396 checked396
    hw (he.trans rhsChecked396) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 397. -/
noncomputable def lambdas397 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000002800002000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000020000020800000400000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000a00000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 397. -/
noncomputable def rhs397 : Nat := 0x6db000036900024900000900000012036d80000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked397 : reconX topRColumns 0x1006400400000001204140740080100020002000030 = rhs397 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 397. -/
theorem initialChecked397 : checkSearchInitial 8 180 13 rows397 lambdas397 0x100 0x1006400400000001204140740080100020002000030 rhs397 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 397 has a listed outside support. -/
theorem complete397 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1006400400000001204140740080100020002000030)
    (hweight : bitCount 180 (outsideMask word 0x1006400400000001204140740080100020002000030) ≤ 1) :
    outsideMask word 0x1006400400000001204140740080100020002000030 ∈ allowed397 := by
  exact outside_mem_of_search 8 180 13 rows397 lambdas397 0x100 0x1006400400000001204140740080100020002000030 rhs397 1
    topEColumns topETransposeColumns tree397 allowed397 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked397 checked397
    hw (he.trans rhsChecked397) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 398. -/
noncomputable def lambdas398 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 398. -/
noncomputable def rhs398 : Nat := 0x3f000db60000002400000000126c0000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked398 : reconX topRColumns 0x1009001000007e00e00240040000188000008000000 = rhs398 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 398. -/
theorem initialChecked398 : checkSearchInitial 8 180 11 rows398 lambdas398 0x10 0x1009001000007e00e00240040000188000008000000 rhs398 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 398 has a listed outside support. -/
theorem complete398 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1009001000007e00e00240040000188000008000000)
    (hweight : bitCount 180 (outsideMask word 0x1009001000007e00e00240040000188000008000000) ≤ 1) :
    outsideMask word 0x1009001000007e00e00240040000188000008000000 ∈ allowed398 := by
  exact outside_mem_of_search 8 180 11 rows398 lambdas398 0x10 0x1009001000007e00e00240040000188000008000000 rhs398 1
    topEColumns topETransposeColumns tree398 allowed398 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked398 checked398
    hw (he.trans rhsChecked398) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 399. -/
noncomputable def lambdas399 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000002000003000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000208000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 399. -/
noncomputable def rhs399 : Nat := 0x6db000dbf00001b4800006c0000240000000012da4

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked399 : reconX topRColumns 0x100a0010000000000032807400c0150018008000000 = rhs399 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 399. -/
theorem initialChecked399 : checkSearchInitial 8 180 11 rows399 lambdas399 0x20 0x100a0010000000000032807400c0150018008000000 rhs399 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 399 has a listed outside support. -/
theorem complete399 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x100a0010000000000032807400c0150018008000000)
    (hweight : bitCount 180 (outsideMask word 0x100a0010000000000032807400c0150018008000000) ≤ 1) :
    outsideMask word 0x100a0010000000000032807400c0150018008000000 ∈ allowed399 := by
  exact outside_mem_of_search 8 180 11 rows399 lambdas399 0x20 0x100a0010000000000032807400c0150018008000000 rhs399 1
    topEColumns topETransposeColumns tree399 allowed399 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked399 checked399
    hw (he.trans rhsChecked399) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 400. -/
noncomputable def lambdas400 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 400. -/
noncomputable def rhs400 : Nat := 0x3f000924000009240000000012000000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked400 : reconX topRColumns 0x1012002000007e00e00240040000148000010000000 = rhs400 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 400. -/
theorem initialChecked400 : checkSearchInitial 8 180 11 rows400 lambdas400 0x10 0x1012002000007e00e00240040000148000010000000 rhs400 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 400 has a listed outside support. -/
theorem complete400 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1012002000007e00e00240040000148000010000000)
    (hweight : bitCount 180 (outsideMask word 0x1012002000007e00e00240040000148000010000000) ≤ 1) :
    outsideMask word 0x1012002000007e00e00240040000148000010000000 ∈ allowed400 := by
  exact outside_mem_of_search 8 180 11 rows400 lambdas400 0x10 0x1012002000007e00e00240040000148000010000000 rhs400 1
    topEColumns topETransposeColumns tree400 allowed400 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked400 checked400
    hw (he.trans rhsChecked400) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 401. -/
noncomputable def lambdas401 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000001000001800000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000208000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 401. -/
noncomputable def rhs401 : Nat := 0xb6d00001b000036900000b40000900000000036d80

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked401 : reconX topRColumns 0x1021004000000000005300ac01401a0028020000000 = rhs401 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 401. -/
theorem initialChecked401 : checkSearchInitial 8 180 11 rows401 lambdas401 0x20 0x1021004000000000005300ac01401a0028020000000 rhs401 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 401 has a listed outside support. -/
theorem complete401 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1021004000000000005300ac01401a0028020000000)
    (hweight : bitCount 180 (outsideMask word 0x1021004000000000005300ac01401a0028020000000) ≤ 1) :
    outsideMask word 0x1021004000000000005300ac01401a0028020000000 ∈ allowed401 := by
  exact outside_mem_of_search 8 180 11 rows401 lambdas401 0x20 0x1021004000000000005300ac01401a0028020000000 rhs401 1
    topEColumns topETransposeColumns tree401 allowed401 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked401 checked401
    hw (he.trans rhsChecked401) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 402. -/
noncomputable def lambdas402 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000030000000000000000000000000000000040000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 402. -/
noncomputable def rhs402 : Nat := 0x3f00000000001b240000000012d80000480000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked402 : reconX topRColumns 0x1024004000007e00e002400400000c8000020000000 = rhs402 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 402. -/
theorem initialChecked402 : checkSearchInitial 8 180 11 rows402 lambdas402 0x10 0x1024004000007e00e002400400000c8000020000000 rhs402 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 402 has a listed outside support. -/
theorem complete402 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x1024004000007e00e002400400000c8000020000000)
    (hweight : bitCount 180 (outsideMask word 0x1024004000007e00e002400400000c8000020000000) ≤ 1) :
    outsideMask word 0x1024004000007e00e002400400000c8000020000000 ∈ allowed402 := by
  exact outside_mem_of_search 8 180 11 rows402 lambdas402 0x10 0x1024004000007e00e002400400000c8000020000000 rhs402 1
    topEColumns topETransposeColumns tree402 allowed402 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked402 checked402
    hw (he.trans rhsChecked402) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 403. -/
noncomputable def lambdas403 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 403. -/
noncomputable def rhs403 : Nat := 0x492000012480000000000fe4000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked403 : reconX topRColumns 0x103b80780000000000024018000001000003c000000 = rhs403 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 403. -/
theorem initialChecked403 : checkSearchInitial 8 180 10 rows403 lambdas403 0x8 0x103b80780000000000024018000001000003c000000 rhs403 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 403 has a listed outside support. -/
theorem complete403 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x103b80780000000000024018000001000003c000000)
    (hweight : bitCount 180 (outsideMask word 0x103b80780000000000024018000001000003c000000) ≤ 1) :
    outsideMask word 0x103b80780000000000024018000001000003c000000 ∈ allowed403 := by
  exact outside_mem_of_search 8 180 10 rows403 lambdas403 0x8 0x103b80780000000000024018000001000003c000000 rhs403 1
    topEColumns topETransposeColumns tree403 allowed403 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked403 checked403
    hw (he.trans rhsChecked403) hweight

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

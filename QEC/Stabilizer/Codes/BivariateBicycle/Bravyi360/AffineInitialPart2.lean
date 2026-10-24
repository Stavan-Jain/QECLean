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
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineSearchPart2

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData
open PackedDigits BB.Bravyi360 BB.Bravyi360.FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 204. -/
noncomputable def lambdas204 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000020000000e00000201000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000200000388000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 204. -/
noncomputable def rhs204 : Nat := 0x36d8003690000048000000900002d000924000dbf

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked204 : reconX topRColumns 0x205800a000000004802c0180020020001005000005 = rhs204 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 204. -/
theorem initialChecked204 : checkSearchInitial 8 180 14 rows204 lambdas204 0x42 0x205800a000000004802c0180020020001005000005 rhs204 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 204 has a listed outside support. -/
theorem complete204 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x205800a000000004802c0180020020001005000005)
    (hweight : bitCount 180 (outsideMask word 0x205800a000000004802c0180020020001005000005) ≤ 1) :
    outsideMask word 0x205800a000000004802c0180020020001005000005 ∈ allowed204 := by
  exact outside_mem_of_search 8 180 14 rows204 lambdas204 0x42 0x205800a000000004802c0180020020001005000005 rhs204 1
    topEColumns topETransposeColumns tree204 allowed204 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked204 checked204
    hw (he.trans rhsChecked204) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 205. -/
noncomputable def lambdas205 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000020000000e0000020100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 205. -/
noncomputable def rhs205 : Nat := 0x36d8003648000048000000900002d000000000dad

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked205 : reconX topRColumns 0x205800a00000000900340180010020001005000003 = rhs205 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 205. -/
theorem initialChecked205 : checkSearchInitial 8 180 12 rows205 lambdas205 0x20 0x205800a00000000900340180010020001005000003 rhs205 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 205 has a listed outside support. -/
theorem complete205 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x205800a00000000900340180010020001005000003)
    (hweight : bitCount 180 (outsideMask word 0x205800a00000000900340180010020001005000003) ≤ 1) :
    outsideMask word 0x205800a00000000900340180010020001005000003 ∈ allowed205 := by
  exact outside_mem_of_search 8 180 12 rows205 lambdas205 0x20 0x205800a00000000900340180010020001005000003 rhs205 1
    topEColumns topETransposeColumns tree205 allowed205 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked205 checked205
    hw (he.trans rhsChecked205) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 206. -/
noncomputable def lambdas206 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000020c0000060000000000000000000000000000000400000000000000000000000100000006000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 206. -/
noncomputable def rhs206 : Nat := 0x36d8003fd8000048000000900002d036d80000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked206 : reconX topRColumns 0x205800a00000001200040180070020001005000030 = rhs206 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 206. -/
theorem initialChecked206 : checkSearchInitial 8 180 12 rows206 lambdas206 0x6 0x205800a00000001200040180070020001005000030 rhs206 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 206 has a listed outside support. -/
theorem complete206 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x205800a00000001200040180070020001005000030)
    (hweight : bitCount 180 (outsideMask word 0x205800a00000001200040180070020001005000030) ≤ 1) :
    outsideMask word 0x205800a00000001200040180070020001005000030 ∈ allowed206 := by
  exact outside_mem_of_search 8 180 12 rows206 lambdas206 0x6 0x205800a00000001200040180070020001005000030 rhs206 1
    topEColumns topETransposeColumns tree206 allowed206 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked206 checked206
    hw (he.trans rhsChecked206) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 207. -/
noncomputable def lambdas207 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000100000006000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 207. -/
noncomputable def rhs207 : Nat := 0x36d80d80d8000048000000900026d000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked207 : reconX topRColumns 0x20c801a000000000002401800301a000100d000000 = rhs207 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 207. -/
theorem initialChecked207 : checkSearchInitial 8 180 12 rows207 lambdas207 0x2 0x20c801a000000000002401800301a000100d000000 rhs207 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 207 has a listed outside support. -/
theorem complete207 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x20c801a000000000002401800301a000100d000000)
    (hweight : bitCount 180 (outsideMask word 0x20c801a000000000002401800301a000100d000000) ≤ 1) :
    outsideMask word 0x20c801a000000000002401800301a000100d000000 ∈ allowed207 := by
  exact outside_mem_of_search 8 180 12 rows207 lambdas207 0x2 0x20c801a000000000002401800301a000100d000000 rhs207 1
    topEColumns topETransposeColumns tree207 allowed207 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked207 checked207
    hw (he.trans rhsChecked207) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 208. -/
noncomputable def lambdas208 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000100000006000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 208. -/
noncomputable def rhs208 : Nat := 0x36d80036d8001b48000000900092d000000000db6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked208 : reconX topRColumns 0x221804a000000000002401800300e0001025000000 = rhs208 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 208. -/
theorem initialChecked208 : checkSearchInitial 8 180 12 rows208 lambdas208 0x2 0x221804a000000000002401800300e0001025000000 rhs208 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 208 has a listed outside support. -/
theorem complete208 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x221804a000000000002401800300e0001025000000)
    (hweight : bitCount 180 (outsideMask word 0x221804a000000000002401800300e0001025000000) ≤ 1) :
    outsideMask word 0x221804a000000000002401800300e0001025000000 ∈ allowed208 := by
  exact outside_mem_of_search 8 180 12 rows208 lambdas208 0x2 0x221804a000000000002401800300e0001025000000 rhs208 1
    topEColumns topETransposeColumns tree208 allowed208 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked208 checked208
    hw (he.trans rhsChecked208) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 209. -/
noncomputable def lambdas209 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000008000008200000080000080400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000020800000000000000000000000000001008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000020000030000000000000000000000000000000100000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 209. -/
noncomputable def rhs209 : Nat := 0x3600001b000000240009240000000012480000ff6036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked209 : reconX topRColumns 0x2400000000000d8011046035000201200000000600 = rhs209 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 209. -/
theorem initialChecked209 : checkSearchInitial 8 180 12 rows209 lambdas209 0x1 0x2400000000000d8011046035000201200000000600 rhs209 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 209 has a listed outside support. -/
theorem complete209 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2400000000000d8011046035000201200000000600)
    (hweight : bitCount 180 (outsideMask word 0x2400000000000d8011046035000201200000000600) ≤ 1) :
    outsideMask word 0x2400000000000d8011046035000201200000000600 ∈ allowed209 := by
  exact outside_mem_of_search 8 180 12 rows209 lambdas209 0x1 0x2400000000000d8011046035000201200000000600 rhs209 1
    topEColumns topETransposeColumns tree209 allowed209 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked209 checked209
    hw (he.trans rhsChecked209) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 210. -/
noncomputable def lambdas210 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000003000000000000000000000000000000004000000000000000000000000280000082000000000000000000000004000000040000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 210. -/
noncomputable def rhs210 : Nat := 0x3600003f000000240009240000000012480000936036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked210 : reconX topRColumns 0x2400000000001f8031046031000201200000000000 = rhs210 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 210. -/
theorem initialChecked210 : checkSearchInitial 8 180 11 rows210 lambdas210 0x20 0x2400000000001f8031046031000201200000000000 rhs210 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 210 has a listed outside support. -/
theorem complete210 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2400000000001f8031046031000201200000000000)
    (hweight : bitCount 180 (outsideMask word 0x2400000000001f8031046031000201200000000000) ≤ 1) :
    outsideMask word 0x2400000000001f8031046031000201200000000000 ∈ allowed210 := by
  exact outside_mem_of_search 8 180 11 rows210 lambdas210 0x20 0x2400000000001f8031046031000201200000000000 rhs210 1
    topEColumns topETransposeColumns tree210 allowed210 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked210 checked210
    hw (he.trans rhsChecked210) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 211. -/
noncomputable def lambdas211 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000800000800000022000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000200000000000000020000000800000220000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000200000000000000000000000020000020000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 211. -/
noncomputable def rhs211 : Nat := 0x240db6000012480036fc0000ff600001b000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked211 : reconX topRColumns 0x240098050001001000000200006000600e00140040 = rhs211 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 211. -/
theorem initialChecked211 : checkSearchInitial 8 180 12 rows211 lambdas211 0x40 0x240098050001001000000200006000600e00140040 rhs211 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 211 has a listed outside support. -/
theorem complete211 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x240098050001001000000200006000600e00140040)
    (hweight : bitCount 180 (outsideMask word 0x240098050001001000000200006000600e00140040) ≤ 1) :
    outsideMask word 0x240098050001001000000200006000600e00140040 ∈ allowed211 := by
  exact outside_mem_of_search 8 180 12 rows211 lambdas211 0x40 0x240098050001001000000200006000600e00140040 rhs211 1
    topEColumns topETransposeColumns tree211 allowed211 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked211 checked211
    hw (he.trans rhsChecked211) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 212. -/
noncomputable def lambdas212 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000c000000000000220000000000000000000000000000000000000000400000010000028000000a00000201000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 212. -/
noncomputable def rhs212 : Nat := 0x240db6000012480036900000ff600003f000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked212 : reconX topRColumns 0x2401b8070001001000000200006000000e00040040 = rhs212 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 212. -/
theorem initialChecked212 : checkSearchInitial 8 180 11 rows212 lambdas212 0x22 0x2401b8070001001000000200006000000e00040040 rhs212 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 212 has a listed outside support. -/
theorem complete212 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2401b8070001001000000200006000000e00040040)
    (hweight : bitCount 180 (outsideMask word 0x2401b8070001001000000200006000000e00040040) ≤ 1) :
    outsideMask word 0x2401b8070001001000000200006000000e00040040 ∈ allowed212 := by
  exact outside_mem_of_search 8 180 11 rows212 lambdas212 0x22 0x2401b8070001001000000200006000000e00040040 rhs212 1
    topEColumns topETransposeColumns tree212 allowed212 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked212 checked212
    hw (he.trans rhsChecked212) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 213. -/
noncomputable def lambdas213 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 213. -/
noncomputable def rhs213 : Nat := 0xdb60009364800094800002400004bf000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked213 : reconX topRColumns 0x2405380b80000000000000000060050002005c0000 = rhs213 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 213. -/
theorem initialChecked213 : checkSearchInitial 8 180 9 rows213 lambdas213 0x8 0x2405380b80000000000000000060050002005c0000 rhs213 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 213 has a listed outside support. -/
theorem complete213 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2405380b80000000000000000060050002005c0000)
    (hweight : bitCount 180 (outsideMask word 0x2405380b80000000000000000060050002005c0000) ≤ 1) :
    outsideMask word 0x2405380b80000000000000000060050002005c0000 ∈ allowed213 := by
  exact outside_mem_of_search 8 180 9 rows213 lambdas213 0x8 0x2405380b80000000000000000060050002005c0000 rhs213 1
    topEColumns topETransposeColumns tree213 allowed213 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked213 checked213
    hw (he.trans rhsChecked213) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 214. -/
noncomputable def lambdas214 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 214. -/
noncomputable def rhs214 : Nat := 0xdb600001248001b48000024000093f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked214 : reconX topRColumns 0x2408b81380000000000000000060030002009c0000 = rhs214 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 214. -/
theorem initialChecked214 : checkSearchInitial 8 180 9 rows214 lambdas214 0x8 0x2408b81380000000000000000060030002009c0000 rhs214 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 214 has a listed outside support. -/
theorem complete214 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2408b81380000000000000000060030002009c0000)
    (hweight : bitCount 180 (outsideMask word 0x2408b81380000000000000000060030002009c0000) ≤ 1) :
    outsideMask word 0x2408b81380000000000000000060030002009c0000 ∈ allowed214 := by
  exact outside_mem_of_search 8 180 9 rows214 lambdas214 0x8 0x2408b81380000000000000000060030002009c0000 rhs214 1
    topEColumns topETransposeColumns tree214 allowed214 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked214 checked214
    hw (he.trans rhsChecked214) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 215. -/
noncomputable def lambdas215 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 215. -/
noncomputable def rhs215 : Nat := 0xdb60004920000126c0000240000fe4000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked215 : reconX topRColumns 0x240ea01e0000000000000000006000600200f00000 = rhs215 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 215. -/
theorem initialChecked215 : checkSearchInitial 8 180 10 rows215 lambdas215 0x8 0x240ea01e0000000000000000006000600200f00000 rhs215 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 215 has a listed outside support. -/
theorem complete215 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x240ea01e0000000000000000006000600200f00000)
    (hweight : bitCount 180 (outsideMask word 0x240ea01e0000000000000000006000600200f00000) ≤ 1) :
    outsideMask word 0x240ea01e0000000000000000006000600200f00000 ∈ allowed215 := by
  exact outside_mem_of_search 8 180 10 rows215 lambdas215 0x8 0x240ea01e0000000000000000006000600200f00000 rhs215 1
    topEColumns topETransposeColumns tree215 allowed215 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked215 checked215
    hw (he.trans rhsChecked215) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 216. -/
noncomputable def lambdas216 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 216. -/
noncomputable def rhs216 : Nat := 0xdb60004b6900012240000240000fd2000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked216 : reconX topRColumns 0x240f101d0000000000000000006000a00200e80000 = rhs216 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 216. -/
theorem initialChecked216 : checkSearchInitial 8 180 10 rows216 lambdas216 0x8 0x240f101d0000000000000000006000a00200e80000 rhs216 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 216 has a listed outside support. -/
theorem complete216 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x240f101d0000000000000000006000a00200e80000)
    (hweight : bitCount 180 (outsideMask word 0x240f101d0000000000000000006000a00200e80000) ≤ 1) :
    outsideMask word 0x240f101d0000000000000000006000a00200e80000 ∈ allowed216 := by
  exact outside_mem_of_search 8 180 10 rows216 lambdas216 0x8 0x240f101d0000000000000000006000a00200e80000 rhs216 1
    topEColumns topETransposeColumns tree216 allowed216 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked216 checked216
    hw (he.trans rhsChecked216) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 217. -/
noncomputable def lambdas217 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 217. -/
noncomputable def rhs217 : Nat := 0xb400006f690001b2400120000006d2000000024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked217 : reconX topRColumns 0x2500d00000000000900a8028001a02000680000000 = rhs217 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 217. -/
theorem initialChecked217 : checkSearchInitial 8 180 12 rows217 lambdas217 0x4 0x2500d00000000000900a8028001a02000680000000 rhs217 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 217 has a listed outside support. -/
theorem complete217 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2500d00000000000900a8028001a02000680000000)
    (hweight : bitCount 180 (outsideMask word 0x2500d00000000000900a8028001a02000680000000) ≤ 1) :
    outsideMask word 0x2500d00000000000900a8028001a02000680000000 ∈ allowed217 := by
  exact outside_mem_of_search 8 180 12 rows217 lambdas217 0x4 0x2500d00000000000900a8028001a02000680000000 rhs217 1
    topEColumns topETransposeColumns tree217 allowed217 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked217 checked217
    hw (he.trans rhsChecked217) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 218. -/
noncomputable def lambdas218 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000080000002800000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000400000000000000000000000000000020000022000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 218. -/
noncomputable def rhs218 : Nat := 0x6c0000fe400001200001b00000048092400001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked218 : reconX topRColumns 0x2800800000004800580d8008006003000400005000 = rhs218 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 218. -/
theorem initialChecked218 : checkSearchInitial 8 180 12 rows218 lambdas218 0x1 0x2800800000004800580d8008006003000400005000 rhs218 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 218 has a listed outside support. -/
theorem complete218 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2800800000004800580d8008006003000400005000)
    (hweight : bitCount 180 (outsideMask word 0x2800800000004800580d8008006003000400005000) ≤ 1) :
    outsideMask word 0x2800800000004800580d8008006003000400005000 ∈ allowed218 := by
  exact outside_mem_of_search 8 180 12 rows218 lambdas218 0x1 0x2800800000004800580d8008006003000400005000 rhs218 1
    topEColumns topETransposeColumns tree218 allowed218 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked218 checked218
    hw (he.trans rhsChecked218) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 219. -/
noncomputable def lambdas219 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000080000002800000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000400000000000000000000000000000030000002000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 219. -/
noncomputable def rhs219 : Nat := 0x6c0000da400001200001b00000048049200001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked219 : reconX topRColumns 0x2800800000006c00180d8000006003000400003000 = rhs219 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 219. -/
theorem initialChecked219 : checkSearchInitial 8 180 12 rows219 lambdas219 0x1 0x2800800000006c00180d8000006003000400003000 rhs219 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 219 has a listed outside support. -/
theorem complete219 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2800800000006c00180d8000006003000400003000)
    (hweight : bitCount 180 (outsideMask word 0x2800800000006c00180d8000006003000400003000) ≤ 1) :
    outsideMask word 0x2800800000006c00180d8000006003000400003000 ∈ allowed219 := by
  exact outside_mem_of_search 8 180 12 rows219 lambdas219 0x1 0x2800800000006c00180d8000006003000400003000 rhs219 1
    topEColumns topETransposeColumns tree219 allowed219 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked219 checked219
    hw (he.trans rhsChecked219) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 220. -/
noncomputable def lambdas220 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 220. -/
noncomputable def rhs220 : Nat := 0xb400006e4d8001b0000120000006c9000000024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked220 : reconX topRColumns 0x2880c80000000000900a8028001c02000640000000 = rhs220 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 220. -/
theorem initialChecked220 : checkSearchInitial 8 180 12 rows220 lambdas220 0x4 0x2880c80000000000900a8028001c02000640000000 rhs220 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 220 has a listed outside support. -/
theorem complete220 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2880c80000000000900a8028001c02000640000000)
    (hweight : bitCount 180 (outsideMask word 0x2880c80000000000900a8028001c02000640000000) ≤ 1) :
    outsideMask word 0x2880c80000000000900a8028001c02000640000000 ∈ allowed220 := by
  exact outside_mem_of_search 8 180 12 rows220 lambdas220 0x4 0x2880c80000000000900a8028001c02000640000000 rhs220 1
    topEColumns topETransposeColumns tree220 allowed220 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked220 checked220
    hw (he.trans rhsChecked220) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 221. -/
noncomputable def lambdas221 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000c0000003100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 221. -/
noncomputable def rhs221 : Nat := 0xda44800126c000048000025b00003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked221 : reconX topRColumns 0x2981a00380000000000000000066000002c01c0000 = rhs221 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 221. -/
theorem initialChecked221 : checkSearchInitial 8 180 12 rows221 lambdas221 0x20 0x2981a00380000000000000000066000002c01c0000 rhs221 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 221 has a listed outside support. -/
theorem complete221 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2981a00380000000000000000066000002c01c0000)
    (hweight : bitCount 180 (outsideMask word 0x2981a00380000000000000000066000002c01c0000) ≤ 1) :
    outsideMask word 0x2981a00380000000000000000066000002c01c0000 ∈ allowed221 := by
  exact outside_mem_of_search 8 180 12 rows221 lambdas221 0x20 0x2981a00380000000000000000066000002c01c0000 rhs221 1
    topEColumns topETransposeColumns tree221 allowed221 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked221 checked221
    hw (he.trans rhsChecked221) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 222. -/
noncomputable def lambdas222 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 222. -/
noncomputable def rhs222 : Nat := 0xb400006d200002dd800120000006c0000009024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked222 : reconX topRColumns 0x2c00880080000000900a8028001002c00600040000 = rhs222 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 222. -/
theorem initialChecked222 : checkSearchInitial 8 180 12 rows222 lambdas222 0x4 0x2c00880080000000900a8028001002c00600040000 rhs222 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 222 has a listed outside support. -/
theorem complete222 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c00880080000000900a8028001002c00600040000)
    (hweight : bitCount 180 (outsideMask word 0x2c00880080000000900a8028001002c00600040000) ≤ 1) :
    outsideMask word 0x2c00880080000000900a8028001002c00600040000 ∈ allowed222 := by
  exact outside_mem_of_search 8 180 12 rows222 lambdas222 0x4 0x2c00880080000000900a8028001002c00600040000 rhs222 1
    topEColumns topETransposeColumns tree222 allowed222 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked222 checked222
    hw (he.trans rhsChecked222) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 223. -/
noncomputable def lambdas223 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000041000000000000000000000000000000804000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 223. -/
noncomputable def rhs223 : Nat := 0xb400006c000001b0000120000006c0024900024b40024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked223 : reconX topRColumns 0x2c00c00000000900800a802a001002000600000a00 = rhs223 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 223. -/
theorem initialChecked223 : checkSearchInitial 8 180 12 rows223 lambdas223 0x4 0x2c00c00000000900800a802a001002000600000a00 rhs223 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 223 has a listed outside support. -/
theorem complete223 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c00c00000000900800a802a001002000600000a00)
    (hweight : bitCount 180 (outsideMask word 0x2c00c00000000900800a802a001002000600000a00) ≤ 1) :
    outsideMask word 0x2c00c00000000900800a802a001002000600000a00 ∈ allowed223 := by
  exact outside_mem_of_search 8 180 12 rows223 lambdas223 0x4 0x2c00c00000000900800a802a001002000600000a00 rhs223 1
    topEColumns topETransposeColumns tree223 allowed223 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked223 checked223
    hw (he.trans rhsChecked223) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 224. -/
noncomputable def lambdas224 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000003000001000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 224. -/
noncomputable def rhs224 : Nat := 0xb4000049200001b0000120000006c0db6000024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked224 : reconX topRColumns 0x2c00c00000002400d00a8020001002000600006000 = rhs224 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 224. -/
theorem initialChecked224 : checkSearchInitial 8 180 13 rows224 lambdas224 0x20 0x2c00c00000002400d00a8020001002000600006000 rhs224 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 224 has a listed outside support. -/
theorem complete224 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c00c00000002400d00a8020001002000600006000)
    (hweight : bitCount 180 (outsideMask word 0x2c00c00000002400d00a8020001002000600006000) ≤ 1) :
    outsideMask word 0x2c00c00000002400d00a8020001002000600006000 ∈ allowed224 := by
  exact outside_mem_of_search 8 180 13 rows224 lambdas224 0x20 0x2c00c00000002400d00a8020001002000600006000 rhs224 1
    topEColumns topETransposeColumns tree224 allowed224 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked224 checked224
    hw (he.trans rhsChecked224) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 225. -/
noncomputable def lambdas225 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000030000010000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000400000000000000000000000000000820000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 225. -/
noncomputable def rhs225 : Nat := 0xb4000025200001b0000120000006c092400002d900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked225 : reconX topRColumns 0x2c00c00000004800100a8038001002000600005000 = rhs225 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 225. -/
theorem initialChecked225 : checkSearchInitial 8 180 13 rows225 lambdas225 0x40 0x2c00c00000004800100a8038001002000600005000 rhs225 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 225 has a listed outside support. -/
theorem complete225 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c00c00000004800100a8038001002000600005000)
    (hweight : bitCount 180 (outsideMask word 0x2c00c00000004800100a8038001002000600005000) ≤ 1) :
    outsideMask word 0x2c00c00000004800100a8038001002000600005000 ∈ allowed225 := by
  exact outside_mem_of_search 8 180 13 rows225 lambdas225 0x40 0x2c00c00000004800100a8038001002000600005000 rhs225 1
    topEColumns topETransposeColumns tree225 allowed225 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked225 checked225
    hw (he.trans rhsChecked225) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 226. -/
noncomputable def lambdas226 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000003000001000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 226. -/
noncomputable def rhs226 : Nat := 0xb40000fd200001b0000120000006c000000003f900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked226 : reconX topRColumns 0x2c00c00000009001900a8008001002000600003000 = rhs226 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 226. -/
theorem initialChecked226 : checkSearchInitial 8 180 13 rows226 lambdas226 0x20 0x2c00c00000009001900a8008001002000600003000 rhs226 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 226 has a listed outside support. -/
theorem complete226 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c00c00000009001900a8008001002000600003000)
    (hweight : bitCount 180 (outsideMask word 0x2c00c00000009001900a8008001002000600003000) ≤ 1) :
    outsideMask word 0x2c00c00000009001900a8008001002000600003000 ∈ allowed226 := by
  exact outside_mem_of_search 8 180 13 rows226 lambdas226 0x20 0x2c00c00000009001900a8008001002000600003000 rhs226 1
    topEColumns topETransposeColumns tree226 allowed226 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked226 checked226
    hw (he.trans rhsChecked226) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 227. -/
noncomputable def lambdas227 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000080000002000001000000008000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 227. -/
noncomputable def rhs227 : Nat := 0xb400006d200093f00001b0000006c0000480024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked227 : reconX topRColumns 0x2c04400800000000900a8028001007000600400000 = rhs227 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 227. -/
theorem initialChecked227 : checkSearchInitial 8 180 12 rows227 lambdas227 0x4 0x2c04400800000000900a8028001007000600400000 rhs227 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 227 has a listed outside support. -/
theorem complete227 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c04400800000000900a8028001007000600400000)
    (hweight : bitCount 180 (outsideMask word 0x2c04400800000000900a8028001007000600400000) ≤ 1) :
    outsideMask word 0x2c04400800000000900a8028001007000600400000 ∈ allowed227 := by
  exact outside_mem_of_search 8 180 12 rows227 lambdas227 0x4 0x2c04400800000000900a8028001007000600400000 rhs227 1
    topEColumns topETransposeColumns tree227 allowed227 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked227 checked227
    hw (he.trans rhsChecked227) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 228. -/
noncomputable def lambdas228 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000820000e000000386000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 228. -/
noncomputable def rhs228 : Nat := 0xb400006d200048900001b0000006c00006c0024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked228 : reconX topRColumns 0x2c06000c00000000900a8028001001000600600000 = rhs228 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 228. -/
theorem initialChecked228 : checkSearchInitial 8 180 14 rows228 lambdas228 0x8 0x2c06000c00000000900a8028001001000600600000 rhs228 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 228 has a listed outside support. -/
theorem complete228 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c06000c00000000900a8028001001000600600000)
    (hweight : bitCount 180 (outsideMask word 0x2c06000c00000000900a8028001001000600600000) ≤ 1) :
    outsideMask word 0x2c06000c00000000900a8028001001000600600000 ∈ allowed228 := by
  exact outside_mem_of_search 8 180 14 rows228 lambdas228 0x8 0x2c06000c00000000900a8028001001000600600000 rhs228 1
    topEColumns topETransposeColumns tree228 allowed228 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked228 checked228
    hw (he.trans rhsChecked228) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 229. -/
noncomputable def lambdas229 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000800000c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 229. -/
noncomputable def rhs229 : Nat := 0xb400006d200001b0000090000006c0000900024900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked229 : reconX topRColumns 0x2c09c01000000000900a8028001001000600800000 = rhs229 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 229. -/
theorem initialChecked229 : checkSearchInitial 8 180 12 rows229 lambdas229 0x4 0x2c09c01000000000900a8028001001000600800000 rhs229 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 229 has a listed outside support. -/
theorem complete229 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2c09c01000000000900a8028001001000600800000)
    (hweight : bitCount 180 (outsideMask word 0x2c09c01000000000900a8028001001000600800000) ≤ 1) :
    outsideMask word 0x2c09c01000000000900a8028001001000600800000 ∈ allowed229 := by
  exact outside_mem_of_search 8 180 12 rows229 lambdas229 0x4 0x2c09c01000000000900a8028001001000600800000 rhs229 1
    topEColumns topETransposeColumns tree229 allowed229 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked229 checked229
    hw (he.trans rhsChecked229) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 230. -/
noncomputable def lambdas230 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000c000000310000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 230. -/
noncomputable def rhs230 : Nat := 0xd929000126c000048000025200003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked230 : reconX topRColumns 0x2d01a8038000000000000000006a000002801c0000 = rhs230 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 230. -/
theorem initialChecked230 : checkSearchInitial 8 180 11 rows230 lambdas230 0x10 0x2d01a8038000000000000000006a000002801c0000 rhs230 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 230 has a listed outside support. -/
theorem complete230 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x2d01a8038000000000000000006a000002801c0000)
    (hweight : bitCount 180 (outsideMask word 0x2d01a8038000000000000000006a000002801c0000) ≤ 1) :
    outsideMask word 0x2d01a8038000000000000000006a000002801c0000 ∈ allowed230 := by
  exact outside_mem_of_search 8 180 11 rows230 lambdas230 0x10 0x2d01a8038000000000000000006a000002801c0000 rhs230 1
    topEColumns topETransposeColumns tree230 allowed230 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked230 checked230
    hw (he.trans rhsChecked230) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 231. -/
noncomputable def lambdas231 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000004000000180000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000800000000000000000000000000000000000020000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 231. -/
noncomputable def rhs231 : Nat := 0xb400006c000027600002d000000900000000d80d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked231 : reconX topRColumns 0x30010000000000032812802800e005000800000006 = rhs231 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 231. -/
theorem initialChecked231 : checkSearchInitial 8 180 11 rows231 lambdas231 0x80 0x30010000000000032812802800e005000800000006 rhs231 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 231 has a listed outside support. -/
theorem complete231 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x30010000000000032812802800e005000800000006)
    (hweight : bitCount 180 (outsideMask word 0x30010000000000032812802800e005000800000006) ≤ 1) :
    outsideMask word 0x30010000000000032812802800e005000800000006 ∈ allowed231 := by
  exact outside_mem_of_search 8 180 11 rows231 lambdas231 0x80 0x30010000000000032812802800e005000800000006 rhs231 1
    topEColumns topETransposeColumns tree231 allowed231 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked231 checked231
    hw (he.trans rhsChecked231) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 232. -/
noncomputable def lambdas232 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000040000001800000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000100000100000008000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000028000020000020800000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 232. -/
noncomputable def rhs232 : Nat := 0xb400006c000093600002d000000900000000036d8002d

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked232 : reconX topRColumns 0x300100000000000868068028026005000800000003 = rhs232 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 232. -/
theorem initialChecked232 : checkSearchInitial 8 180 12 rows232 lambdas232 0x101 0x300100000000000868068028026005000800000003 rhs232 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 232 has a listed outside support. -/
theorem complete232 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300100000000000868068028026005000800000003)
    (hweight : bitCount 180 (outsideMask word 0x300100000000000868068028026005000800000003) ≤ 1) :
    outsideMask word 0x300100000000000868068028026005000800000003 ∈ allowed232 := by
  exact outside_mem_of_search 8 180 12 rows232 lambdas232 0x101 0x300100000000000868068028026005000800000003 rhs232 1
    topEColumns topETransposeColumns tree232 allowed232 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked232 checked232
    hw (he.trans rhsChecked232) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 233. -/
noncomputable def lambdas233 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000004000000180000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000c000000300000200000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000800000000000000000000000000000010000022000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 233. -/
noncomputable def rhs233 : Nat := 0xb40000fc000003600002d00000090000000002dd80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked233 : reconX topRColumns 0x300100000000900068168008006005000800003000 = rhs233 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 233. -/
theorem initialChecked233 : checkSearchInitial 8 180 12 rows233 lambdas233 0x100 0x300100000000900068168008006005000800003000 rhs233 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 233 has a listed outside support. -/
theorem complete233 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300100000000900068168008006005000800003000)
    (hweight : bitCount 180 (outsideMask word 0x300100000000900068168008006005000800003000) ≤ 1) :
    outsideMask word 0x300100000000900068168008006005000800003000 ∈ allowed233 := by
  exact outside_mem_of_search 8 180 12 rows233 lambdas233 0x100 0x300100000000900068168008006005000800003000 rhs233 1
    topEColumns topETransposeColumns tree233 allowed233 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked233 checked233
    hw (he.trans rhsChecked233) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 234. -/
noncomputable def lambdas234 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000040000001000002800000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000180000080000004000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 234. -/
noncomputable def rhs234 : Nat := 0xb400006c0000912000024000000900000480036d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked234 : reconX topRColumns 0x300580080000000168168028006000000800400000 = rhs234 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 234. -/
theorem initialChecked234 : checkSearchInitial 8 180 15 rows234 lambdas234 0x10 0x300580080000000168168028006000000800400000 rhs234 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 234 has a listed outside support. -/
theorem complete234 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300580080000000168168028006000000800400000)
    (hweight : bitCount 180 (outsideMask word 0x300580080000000168168028006000000800400000) ≤ 1) :
    outsideMask word 0x300580080000000168168028006000000800400000 ∈ allowed234 := by
  exact outside_mem_of_search 8 180 15 rows234 lambdas234 0x10 0x300580080000000168168028006000000800400000 rhs234 1
    topEColumns topETransposeColumns tree234 allowed234 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked234 checked234
    hw (he.trans rhsChecked234) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 235. -/
noncomputable def lambdas235 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000400000010000011000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000400000010000020000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000028000020000020800000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 235. -/
noncomputable def rhs235 : Nat := 0xb400006c0000036000036000000900000900036d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked235 : reconX topRColumns 0x300800100000000168168028006006000800800000 = rhs235 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 235. -/
theorem initialChecked235 : checkSearchInitial 8 180 13 rows235 lambdas235 0x201 0x300800100000000168168028006006000800800000 rhs235 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 235 has a listed outside support. -/
theorem complete235 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x300800100000000168168028006006000800800000)
    (hweight : bitCount 180 (outsideMask word 0x300800100000000168168028006006000800800000) ≤ 1) :
    outsideMask word 0x300800100000000168168028006006000800800000 ∈ allowed235 := by
  exact outside_mem_of_search 8 180 13 rows235 lambdas235 0x201 0x300800100000000168168028006006000800800000 rhs235 1
    topEColumns topETransposeColumns tree235 allowed235 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked235 checked235
    hw (he.trans rhsChecked235) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 236. -/
noncomputable def lambdas236 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000060000020000000100000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 236. -/
noncomputable def rhs236 : Nat := 0x36000036d8000048000924000002d000000000db6036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked236 : reconX topRColumns 0x328028000000000009046036000801200140000000 = rhs236 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 236. -/
theorem initialChecked236 : checkSearchInitial 8 180 12 rows236 lambdas236 0x20 0x328028000000000009046036000801200140000000 rhs236 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 236 has a listed outside support. -/
theorem complete236 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x328028000000000009046036000801200140000000)
    (hweight : bitCount 180 (outsideMask word 0x328028000000000009046036000801200140000000) ≤ 1) :
    outsideMask word 0x328028000000000009046036000801200140000000 ∈ allowed236 := by
  exact outside_mem_of_search 8 180 12 rows236 lambdas236 0x20 0x328028000000000009046036000801200140000000 rhs236 1
    topEColumns topETransposeColumns tree236 allowed236 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked236 checked236
    hw (he.trans rhsChecked236) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 237. -/
noncomputable def lambdas237 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000c0000003100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 237. -/
noncomputable def rhs237 : Nat := 0xd80d8001224000048000026d00003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked237 : reconX topRColumns 0x328190038000000000000000006a000003401c0000 = rhs237 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 237. -/
theorem initialChecked237 : checkSearchInitial 8 180 12 rows237 lambdas237 0x20 0x328190038000000000000000006a000003401c0000 rhs237 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 237 has a listed outside support. -/
theorem complete237 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x328190038000000000000000006a000003401c0000)
    (hweight : bitCount 180 (outsideMask word 0x328190038000000000000000006a000003401c0000) ≤ 1) :
    outsideMask word 0x328190038000000000000000006a000003401c0000 ∈ allowed237 := by
  exact outside_mem_of_search 8 180 12 rows237 lambdas237 0x20 0x328190038000000000000000006a000003401c0000 rhs237 1
    topEColumns topETransposeColumns tree237 allowed237 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked237 checked237
    hw (he.trans rhsChecked237) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 238. -/
noncomputable def lambdas238 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000c000000310000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 238. -/
noncomputable def rhs238 : Nat := 0xdb600001224000048000026400003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked238 : reconX topRColumns 0x3601980380000000000000000066000003001c0000 = rhs238 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 238. -/
theorem initialChecked238 : checkSearchInitial 8 180 11 rows238 lambdas238 0x10 0x3601980380000000000000000066000003001c0000 rhs238 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 238 has a listed outside support. -/
theorem complete238 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3601980380000000000000000066000003001c0000)
    (hweight : bitCount 180 (outsideMask word 0x3601980380000000000000000066000003001c0000) ≤ 1) :
    outsideMask word 0x3601980380000000000000000066000003001c0000 ∈ allowed238 := by
  exact outside_mem_of_search 8 180 11 rows238 lambdas238 0x10 0x3601980380000000000000000066000003001c0000 rhs238 1
    topEColumns topETransposeColumns tree238 allowed238 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked238 checked238
    hw (he.trans rhsChecked238) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 239. -/
noncomputable def lambdas239 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 239. -/
noncomputable def rhs239 : Nat := 0xda448001200000024000027f00001b000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked239 : reconX topRColumns 0x3b80a00180000000000000000060006003c00c0000 = rhs239 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 239. -/
theorem initialChecked239 : checkSearchInitial 8 180 11 rows239 lambdas239 0x80 0x3b80a00180000000000000000060006003c00c0000 rhs239 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 239 has a listed outside support. -/
theorem complete239 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3b80a00180000000000000000060006003c00c0000)
    (hweight : bitCount 180 (outsideMask word 0x3b80a00180000000000000000060006003c00c0000) ≤ 1) :
    outsideMask word 0x3b80a00180000000000000000060006003c00c0000 ∈ allowed239 := by
  exact outside_mem_of_search 8 180 11 rows239 lambdas239 0x80 0x3b80a00180000000000000000060006003c00c0000 rhs239 1
    topEColumns topETransposeColumns tree239 allowed239 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked239 checked239
    hw (he.trans rhsChecked239) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 240. -/
noncomputable def lambdas240 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 240. -/
noncomputable def rhs240 : Nat := 0xda4480024d8000024000027f000012000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked240 : reconX topRColumns 0x3b80e8010000000000000000006000a003c0080000 = rhs240 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 240. -/
theorem initialChecked240 : checkSearchInitial 8 180 10 rows240 lambdas240 0x40 0x3b80e8010000000000000000006000a003c0080000 rhs240 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 240 has a listed outside support. -/
theorem complete240 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3b80e8010000000000000000006000a003c0080000)
    (hweight : bitCount 180 (outsideMask word 0x3b80e8010000000000000000006000a003c0080000) ≤ 1) :
    outsideMask word 0x3b80e8010000000000000000006000a003c0080000 ∈ allowed240 := by
  exact outside_mem_of_search 8 180 10 rows240 lambdas240 0x40 0x3b80e8010000000000000000006000a003c0080000 rhs240 1
    topEColumns topETransposeColumns tree240 allowed240 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked240 checked240
    hw (he.trans rhsChecked240) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 241. -/
noncomputable def lambdas241 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 241. -/
noncomputable def rhs241 : Nat := 0xda44800369000006c000027f00002d000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked241 : reconX topRColumns 0x3b8110028000000000000000006000a003c0140000 = rhs241 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 241. -/
theorem initialChecked241 : checkSearchInitial 8 180 11 rows241 lambdas241 0x80 0x3b8110028000000000000000006000a003c0140000 rhs241 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 241 has a listed outside support. -/
theorem complete241 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3b8110028000000000000000006000a003c0140000)
    (hweight : bitCount 180 (outsideMask word 0x3b8110028000000000000000006000a003c0140000) ≤ 1) :
    outsideMask word 0x3b8110028000000000000000006000a003c0140000 ∈ allowed241 := by
  exact outside_mem_of_search 8 180 11 rows241 lambdas241 0x80 0x3b8110028000000000000000006000a003c0140000 rhs241 1
    topEColumns topETransposeColumns tree241 allowed241 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked241 checked241
    hw (he.trans rhsChecked241) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 242. -/
noncomputable def lambdas242 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 242. -/
noncomputable def rhs242 : Nat := 0xda44800004800006c000027f000024000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked242 : reconX topRColumns 0x3b81580200000000000000000060006003c0100000 = rhs242 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 242. -/
theorem initialChecked242 : checkSearchInitial 8 180 10 rows242 lambdas242 0x40 0x3b81580200000000000000000060006003c0100000 rhs242 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 242 has a listed outside support. -/
theorem complete242 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x3b81580200000000000000000060006003c0100000)
    (hweight : bitCount 180 (outsideMask word 0x3b81580200000000000000000060006003c0100000) ≤ 1) :
    outsideMask word 0x3b81580200000000000000000060006003c0100000 ∈ allowed242 := by
  exact outside_mem_of_search 8 180 10 rows242 lambdas242 0x40 0x3b81580200000000000000000060006003c0100000 rhs242 1
    topEColumns topETransposeColumns tree242 allowed242 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked242 checked242
    hw (he.trans rhsChecked242) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 243. -/
noncomputable def lambdas243 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000a0000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000600000410000000000000000000000020000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 243. -/
noncomputable def rhs243 : Nat := 0xb40009d80000012000012000000036912000036900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked243 : reconX topRColumns 0x400000000001dc03500a8050002002000000030000 = rhs243 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 243. -/
theorem initialChecked243 : checkSearchInitial 8 180 12 rows243 lambdas243 0x20 0x400000000001dc03500a8050002002000000030000 rhs243 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 243 has a listed outside support. -/
theorem complete243 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x400000000001dc03500a8050002002000000030000)
    (hweight : bitCount 180 (outsideMask word 0x400000000001dc03500a8050002002000000030000) ≤ 1) :
    outsideMask word 0x400000000001dc03500a8050002002000000030000 ∈ allowed243 := by
  exact outside_mem_of_search 8 180 12 rows243 lambdas243 0x20 0x400000000001dc03500a8050002002000000030000 rhs243 1
    topEColumns topETransposeColumns tree243 allowed243 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked243 checked243
    hw (he.trans rhsChecked243) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 244. -/
noncomputable def lambdas244 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000002000006000004000004100000000000200000040000000000000000000000000000000c00000400000410000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000a000000000000000000000000000000020000000000000000000000000200000800000010000010000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 244. -/
noncomputable def rhs244 : Nat := 0x24b40000d80000480000012036036000492000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked244 : reconX topRColumns 0x400400000001040d80540108010010002000036000 = rhs244 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 244. -/
theorem initialChecked244 : checkSearchInitial 8 180 16 rows244 lambdas244 0x11 0x400400000001040d80540108010010002000036000 rhs244 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 244 has a listed outside support. -/
theorem complete244 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x400400000001040d80540108010010002000036000)
    (hweight : bitCount 180 (outsideMask word 0x400400000001040d80540108010010002000036000) ≤ 1) :
    outsideMask word 0x400400000001040d80540108010010002000036000 ∈ allowed244 := by
  exact outside_mem_of_search 8 180 16 rows244 lambdas244 0x11 0x400400000001040d80540108010010002000036000 rhs244 1
    topEColumns topETransposeColumns tree244 allowed244 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked244 checked244
    hw (he.trans rhsChecked244) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 245. -/
noncomputable def lambdas245 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000c000004000004100000000000000000010000000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 245. -/
noncomputable def rhs245 : Nat := 0x24900000fc0000480000012036d80000924000936

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked245 : reconX topRColumns 0x400400000001200f80500100018010002000030006 = rhs245 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 245. -/
theorem initialChecked245 : checkSearchInitial 8 180 15 rows245 lambdas245 0x2 0x400400000001200f80500100018010002000030006 rhs245 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 245 has a listed outside support. -/
theorem complete245 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x400400000001200f80500100018010002000030006)
    (hweight : bitCount 180 (outsideMask word 0x400400000001200f80500100018010002000030006) ≤ 1) :
    outsideMask word 0x400400000001200f80500100018010002000030006 ∈ allowed245 := by
  exact outside_mem_of_search 8 180 15 rows245 lambdas245 0x2 0x400400000001200f80500100018010002000030006 rhs245 1
    topEColumns topETransposeColumns tree245 allowed245 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked245 checked245
    hw (he.trans rhsChecked245) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 246. -/
noncomputable def lambdas246 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000030000028c4000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000200000288000000400000000000000000000000000000000a00000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 246. -/
noncomputable def rhs246 : Nat := 0x24900012d80000480000012036d80024d92000b76

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked246 : reconX topRColumns 0x4004000000012029c0140100090010002000030028 = rhs246 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 246. -/
theorem initialChecked246 : checkSearchInitial 8 180 13 rows246 lambdas246 0x20 0x4004000000012029c0140100090010002000030028 rhs246 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 246 has a listed outside support. -/
theorem complete246 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x4004000000012029c0140100090010002000030028)
    (hweight : bitCount 180 (outsideMask word 0x4004000000012029c0140100090010002000030028) ≤ 1) :
    outsideMask word 0x4004000000012029c0140100090010002000030028 ∈ allowed246 := by
  exact outside_mem_of_search 8 180 13 rows246 lambdas246 0x20 0x4004000000012029c0140100090010002000030028 rhs246 1
    topEColumns topETransposeColumns tree246 allowed246 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked246 checked246
    hw (he.trans rhsChecked246) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 247. -/
noncomputable def lambdas247 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000020000000c000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 247. -/
noncomputable def rhs247 : Nat := 0x249000126c00006c0000012036d9b000000000924

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked247 : reconX topRColumns 0x403200600001200200480100028008002003030000 = rhs247 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 247. -/
theorem initialChecked247 : checkSearchInitial 8 180 12 rows247 lambdas247 0x2 0x403200600001200200480100028008002003030000 rhs247 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 247 has a listed outside support. -/
theorem complete247 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x403200600001200200480100028008002003030000)
    (hweight : bitCount 180 (outsideMask word 0x403200600001200200480100028008002003030000) ≤ 1) :
    outsideMask word 0x403200600001200200480100028008002003030000 ∈ allowed247 := by
  exact outside_mem_of_search 8 180 12 rows247 lambdas247 0x2 0x403200600001200200480100028008002003030000 rhs247 1
    topEColumns topETransposeColumns tree247 allowed247 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked247 checked247
    hw (he.trans rhsChecked247) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 248. -/
noncomputable def lambdas248 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000080000080400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000008000000300000100800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000800000804000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 248. -/
noncomputable def rhs248 : Nat := 0x90090001bb76000ff600049200001b240000240

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked248 : reconX topRColumns 0x410041010001000000000000005a007805000c8008 = rhs248 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 248. -/
theorem initialChecked248 : checkSearchInitial 8 180 15 rows248 lambdas248 0x80 0x410041010001000000000000005a007805000c8008 rhs248 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 248 has a listed outside support. -/
theorem complete248 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x410041010001000000000000005a007805000c8008)
    (hweight : bitCount 180 (outsideMask word 0x410041010001000000000000005a007805000c8008) ≤ 1) :
    outsideMask word 0x410041010001000000000000005a007805000c8008 ∈ allowed248 := by
  exact outside_mem_of_search 8 180 15 rows248 lambdas248 0x80 0x410041010001000000000000005a007805000c8008 rhs248 1
    topEColumns topETransposeColumns tree248 allowed248 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked248 checked248
    hw (he.trans rhsChecked248) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 249. -/
noncomputable def lambdas249 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008000008040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000080000080000002200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000200000000000000000000000020000020000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 249. -/
noncomputable def rhs249 : Nat := 0x24090090001b6c0036fc000092400001b000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked249 : reconX topRColumns 0x410048050001001000000200005a00600880140040 = rhs249 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 249. -/
theorem initialChecked249 : checkSearchInitial 8 180 13 rows249 lambdas249 0x20 0x410048050001001000000200005a00600880140040 rhs249 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 249 has a listed outside support. -/
theorem complete249 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x410048050001001000000200005a00600880140040)
    (hweight : bitCount 180 (outsideMask word 0x410048050001001000000200005a00600880140040) ≤ 1) :
    outsideMask word 0x410048050001001000000200005a00600880140040 ∈ allowed249 := by
  exact outside_mem_of_search 8 180 13 rows249 lambdas249 0x20 0x410048050001001000000200005a00600880140040 rhs249 1
    topEColumns topETransposeColumns tree249 allowed249 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked249 checked249
    hw (he.trans rhsChecked249) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 250. -/
noncomputable def lambdas250 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000a00000031000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000002000000000000220000000000000000000000000000000000800000020000010000000200000201000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 250. -/
noncomputable def rhs250 : Nat := 0x24090090001b6c003690000092400003f000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked250 : reconX topRColumns 0x410168070001001000000200005a00000880040040 = rhs250 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 250. -/
theorem initialChecked250 : checkSearchInitial 8 180 14 rows250 lambdas250 0x48 0x410168070001001000000200005a00000880040040 rhs250 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 250 has a listed outside support. -/
theorem complete250 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x410168070001001000000200005a00000880040040)
    (hweight : bitCount 180 (outsideMask word 0x410168070001001000000200005a00000880040040) ≤ 1) :
    outsideMask word 0x410168070001001000000200005a00000880040040 ∈ allowed250 := by
  exact outside_mem_of_search 8 180 14 rows250 lambdas250 0x48 0x410168070001001000000200005a00000880040040 rhs250 1
    topEColumns topETransposeColumns tree250 allowed250 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked250 checked250
    hw (he.trans rhsChecked250) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 251. -/
noncomputable def lambdas251 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000c0000040000000200000000000000000000000000000000000000000000000104000000000002010000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000800000020000008000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 251. -/
noncomputable def rhs251 : Nat := 0x936480009ff6000db600049b000000240000240

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked251 : reconX topRColumns 0x458091008001000000000000005600180540008008 = rhs251 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 251. -/
theorem initialChecked251 : checkSearchInitial 8 180 12 rows251 lambdas251 0x20 0x458091008001000000000000005600180540008008 rhs251 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 251 has a listed outside support. -/
theorem complete251 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x458091008001000000000000005600180540008008)
    (hweight : bitCount 180 (outsideMask word 0x458091008001000000000000005600180540008008) ≤ 1) :
    outsideMask word 0x458091008001000000000000005600180540008008 ∈ allowed251 := by
  exact outside_mem_of_search 8 180 12 rows251 lambdas251 0x20 0x458091008001000000000000005600180540008008 rhs251 1
    topEColumns topETransposeColumns tree251 allowed251 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked251 checked251
    hw (he.trans rhsChecked251) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 252. -/
noncomputable def lambdas252 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000020000000800000e040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 252. -/
noncomputable def rhs252 : Nat := 0x240924b40009000036d80000936000db6000012000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked252 : reconX topRColumns 0x48008004800102c005000200a05000000800180100 = rhs252 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 252. -/
theorem initialChecked252 : checkSearchInitial 8 180 14 rows252 lambdas252 0x10 0x48008004800102c005000200a05000000800180100 rhs252 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 252 has a listed outside support. -/
theorem complete252 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x48008004800102c005000200a05000000800180100)
    (hweight : bitCount 180 (outsideMask word 0x48008004800102c005000200a05000000800180100) ≤ 1) :
    outsideMask word 0x48008004800102c005000200a05000000800180100 ∈ allowed252 := by
  exact outside_mem_of_search 8 180 14 rows252 lambdas252 0x10 0x48008004800102c005000200a05000000800180100 rhs252 1
    topEColumns topETransposeColumns tree252 allowed252 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked252 checked252
    hw (he.trans rhsChecked252) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 253. -/
noncomputable def lambdas253 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000020000020000020c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000c00000000000022000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 253. -/
noncomputable def rhs253 : Nat := 0x240924000dad48003690000093600027f000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked253 : reconX topRColumns 0x480338030001001000000200005006000800240040 = rhs253 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 253. -/
theorem initialChecked253 : checkSearchInitial 8 180 11 rows253 lambdas253 0x21 0x480338030001001000000200005006000800240040 rhs253 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 253 has a listed outside support. -/
theorem complete253 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x480338030001001000000200005006000800240040)
    (hweight : bitCount 180 (outsideMask word 0x480338030001001000000200005006000800240040) ≤ 1) :
    outsideMask word 0x480338030001001000000200005006000800240040 ∈ allowed253 := by
  exact outside_mem_of_search 8 180 11 rows253 lambdas253 0x21 0x480338030001001000000200005006000800240040 rhs253 1
    topEColumns topETransposeColumns tree253 allowed253 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked253 checked253
    hw (he.trans rhsChecked253) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 254. -/
noncomputable def lambdas254 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000008000000300000020000000000000000000000000000000000000000000000000000000410000000000008040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 254. -/
noncomputable def rhs254 : Nat := 0x24092400049b00003fd800009360006c0000009000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked254 : reconX topRColumns 0x480640088001001000000200005003000800780040 = rhs254 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 254. -/
theorem initialChecked254 : checkSearchInitial 8 180 13 rows254 lambdas254 0x10 0x480640088001001000000200005003000800780040 rhs254 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 254 has a listed outside support. -/
theorem complete254 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x480640088001001000000200005003000800780040)
    (hweight : bitCount 180 (outsideMask word 0x480640088001001000000200005003000800780040) ≤ 1) :
    outsideMask word 0x480640088001001000000200005003000800780040 ∈ allowed254 := by
  exact outside_mem_of_search 8 180 13 rows254 lambdas254 0x10 0x480640088001001000000200005003000800780040 rhs254 1
    topEColumns topETransposeColumns tree254 allowed254 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked254 checked254
    hw (he.trans rhsChecked254) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 255. -/
noncomputable def lambdas255 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000002000000000000220000000000000000000000000000000000000000000400000020000028000008040000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 255. -/
noncomputable def rhs255 : Nat := 0x936480009936000db60004bf000000240000240

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked255 : reconX topRColumns 0x5780b1008001000000000000005000180440008008 = rhs255 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 255. -/
theorem initialChecked255 : checkSearchInitial 8 180 12 rows255 lambdas255 0x100 0x5780b1008001000000000000005000180440008008 rhs255 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 255 has a listed outside support. -/
theorem complete255 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x5780b1008001000000000000005000180440008008)
    (hweight : bitCount 180 (outsideMask word 0x5780b1008001000000000000005000180440008008) ≤ 1) :
    outsideMask word 0x5780b1008001000000000000005000180440008008 ∈ allowed255 := by
  exact outside_mem_of_search 8 180 12 rows255 lambdas255 0x100 0x5780b1008001000000000000005000180440008008 rhs255 1
    topEColumns topETransposeColumns tree255 allowed255 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked255 checked255
    hw (he.trans rhsChecked255) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 256. -/
noncomputable def lambdas256 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 256. -/
noncomputable def rhs256 : Nat := 0x6c0000240000fdb00001b000000000000000480480000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked256 : reconX topRColumns 0x600000000000000f1811801803b003000000000000 = rhs256 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 256. -/
theorem initialChecked256 : checkSearchInitial 8 180 11 rows256 lambdas256 0x10 0x600000000000000f1811801803b003000000000000 rhs256 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 256 has a listed outside support. -/
theorem complete256 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x600000000000000f1811801803b003000000000000)
    (hweight : bitCount 180 (outsideMask word 0x600000000000000f1811801803b003000000000000) ≤ 1) :
    outsideMask word 0x600000000000000f1811801803b003000000000000 ∈ allowed256 := by
  exact outside_mem_of_search 8 180 11 rows256 lambdas256 0x10 0x600000000000000f1811801803b003000000000000 rhs256 1
    topEColumns topETransposeColumns tree256 allowed256 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked256 checked256
    hw (he.trans rhsChecked256) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 257. -/
noncomputable def lambdas257 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c00000010000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000004000004180000080000080000000000000000000800000000000000000000000000000400000610000008000000000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 257. -/
noncomputable def rhs257 : Nat := 0x6c00006d200001b00001b00000000090090001b6c0012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked257 : reconX topRColumns 0x6000000000004100480d800a003003000000005a00 = rhs257 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 257. -/
theorem initialChecked257 : checkSearchInitial 8 180 13 rows257 lambdas257 0x41 0x6000000000004100480d800a003003000000005a00 rhs257 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 257 has a listed outside support. -/
theorem complete257 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6000000000004100480d800a003003000000005a00)
    (hweight : bitCount 180 (outsideMask word 0x6000000000004100480d800a003003000000005a00) ≤ 1) :
    outsideMask word 0x6000000000004100480d800a003003000000005a00 ∈ allowed257 := by
  exact outside_mem_of_search 8 180 13 rows257 lambdas257 0x41 0x6000000000004100480d800a003003000000005a00 rhs257 1
    topEColumns topETransposeColumns tree257 allowed257 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked257 checked257
    hw (he.trans rhsChecked257) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 258. -/
noncomputable def lambdas258 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c000000100000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000800000c20000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 258. -/
noncomputable def rhs258 : Nat := 0x6c00006c000025b00001b000000000924000dad480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked258 : reconX topRColumns 0x60000000000048021809800800b003000000005006 = rhs258 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 258. -/
theorem initialChecked258 : checkSearchInitial 8 180 14 rows258 lambdas258 0x81 0x60000000000048021809800800b003000000005006 rhs258 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 258 has a listed outside support. -/
theorem complete258 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x60000000000048021809800800b003000000005006)
    (hweight : bitCount 180 (outsideMask word 0x60000000000048021809800800b003000000005006) ≤ 1) :
    outsideMask word 0x60000000000048021809800800b003000000005006 ∈ allowed258 := by
  exact outside_mem_of_search 8 180 14 rows258 lambdas258 0x81 0x60000000000048021809800800b003000000005006 rhs258 1
    topEColumns topETransposeColumns tree258 allowed258 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked258 checked258
    hw (he.trans rhsChecked258) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 259. -/
noncomputable def lambdas259 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c000000100000020000000000000000000000000000000000000000000000000a0000000800000100000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000004000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 259. -/
noncomputable def rhs259 : Nat := 0x6c000049200001b00001b0000000004b690001b6c0012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked259 : reconX topRColumns 0x6000000000006500080d8002003003000000003a00 = rhs259 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 259. -/
theorem initialChecked259 : checkSearchInitial 8 180 13 rows259 lambdas259 0x40 0x6000000000006500080d8002003003000000003a00 rhs259 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 259 has a listed outside support. -/
theorem complete259 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6000000000006500080d8002003003000000003a00)
    (hweight : bitCount 180 (outsideMask word 0x6000000000006500080d8002003003000000003a00) ≤ 1) :
    outsideMask word 0x6000000000006500080d8002003003000000003a00 ∈ allowed259 := by
  exact outside_mem_of_search 8 180 13 rows259 lambdas259 0x40 0x6000000000006500080d8002003003000000003a00 rhs259 1
    topEColumns topETransposeColumns tree259 allowed259 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked259 checked259
    hw (he.trans rhsChecked259) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 260. -/
noncomputable def lambdas260 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c000000100000020000000000000000000000000000000000000000000000000a00000008000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 260. -/
noncomputable def rhs260 : Nat := 0x6c000048900001b00001b0000000004a4d8001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked260 : reconX topRColumns 0x6000000000006880100d8001003003000000003c00 = rhs260 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 260. -/
theorem initialChecked260 : checkSearchInitial 8 180 14 rows260 lambdas260 0x80 0x6000000000006880100d8001003003000000003c00 rhs260 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 260 has a listed outside support. -/
theorem complete260 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6000000000006880100d8001003003000000003c00)
    (hweight : bitCount 180 (outsideMask word 0x6000000000006880100d8001003003000000003c00) ≤ 1) :
    outsideMask word 0x6000000000006880100d8001003003000000003c00 ∈ allowed260 := by
  exact outside_mem_of_search 8 180 14 rows260 lambdas260 0x80 0x6000000000006880100d8001003003000000003c00 rhs260 1
    topEColumns topETransposeColumns tree260 allowed260 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked260 checked260
    hw (he.trans rhsChecked260) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 261. -/
noncomputable def lambdas261 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c000004000000020000000000000000000000000000000000000000000800000400000418000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000010a00010e00000208000000000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 261. -/
noncomputable def rhs261 : Nat := 0x1b4800126c00006c000001b0000000240240006db

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked261 : reconX topRColumns 0x6006000000000020802400c008801800300000002d = rhs261 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 261. -/
theorem initialChecked261 : checkSearchInitial 8 180 15 rows261 lambdas261 0xc0 0x6006000000000020802400c008801800300000002d rhs261 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 261 has a listed outside support. -/
theorem complete261 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6006000000000020802400c008801800300000002d)
    (hweight : bitCount 180 (outsideMask word 0x6006000000000020802400c008801800300000002d) ≤ 1) :
    outsideMask word 0x6006000000000020802400c008801800300000002d ∈ allowed261 := by
  exact outside_mem_of_search 8 180 15 rows261 lambdas261 0xc0 0x6006000000000020802400c008801800300000002d rhs261 1
    topEColumns topETransposeColumns tree261 allowed261 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked261 checked261
    hw (he.trans rhsChecked261) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 262. -/
noncomputable def lambdas262 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000c00000400000002000000000000000000000000000000000000000000080000040000041800000100000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 262. -/
noncomputable def rhs262 : Nat := 0x94800006c00006c000001b024900000b6400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked262 : reconX topRColumns 0x600600000002400080640040008018003000028005 = rhs262 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 262. -/
theorem initialChecked262 : checkSearchInitial 8 180 15 rows262 lambdas262 0x60 0x600600000002400080640040008018003000028005 rhs262 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 262 has a listed outside support. -/
theorem complete262 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x600600000002400080640040008018003000028005)
    (hweight : bitCount 180 (outsideMask word 0x600600000002400080640040008018003000028005) ≤ 1) :
    outsideMask word 0x600600000002400080640040008018003000028005 ∈ allowed262 := by
  exact outside_mem_of_search 8 180 15 rows262 lambdas262 0x60 0x600600000002400080640040008018003000028005 rhs262 1
    topEColumns topETransposeColumns tree262 allowed262 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked262 checked262
    hw (he.trans rhsChecked262) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 263. -/
noncomputable def lambdas263 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000008000000000000110000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000a21000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000400000000000000000000000000000020000022000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 263. -/
noncomputable def rhs263 : Nat := 0x6c00006c000001b00000000000000092490001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked263 : reconX topRColumns 0x6009001000004800580d8008003000000000805000 = rhs263 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 263. -/
theorem initialChecked263 : checkSearchInitial 8 180 12 rows263 lambdas263 0x1 0x6009001000004800580d8008003000000000805000 rhs263 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 263 has a listed outside support. -/
theorem complete263 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6009001000004800580d8008003000000000805000)
    (hweight : bitCount 180 (outsideMask word 0x6009001000004800580d8008003000000000805000) ≤ 1) :
    outsideMask word 0x6009001000004800580d8008003000000000805000 ∈ allowed263 := by
  exact outside_mem_of_search 8 180 12 rows263 lambdas263 0x1 0x6009001000004800580d8008003000000000805000 rhs263 1
    topEColumns topETransposeColumns tree263 allowed263 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked263 checked263
    hw (he.trans rhsChecked263) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 264. -/
noncomputable def lambdas264 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000800000000000011000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000e310000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000400000000000000000000000000000030000002000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 264. -/
noncomputable def rhs264 : Nat := 0x6c000048000001b00000000000000049290001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked264 : reconX topRColumns 0x6009001000006c00180d8000003000000000803000 = rhs264 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 264. -/
theorem initialChecked264 : checkSearchInitial 8 180 12 rows264 lambdas264 0x1 0x6009001000006c00180d8000003000000000803000 rhs264 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 264 has a listed outside support. -/
theorem complete264 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6009001000006c00180d8000003000000000803000)
    (hweight : bitCount 180 (outsideMask word 0x6009001000006c00180d8000003000000000803000) ≤ 1) :
    outsideMask word 0x6009001000006c00180d8000003000000000803000 ∈ allowed264 := by
  exact outside_mem_of_search 8 180 12 rows264 lambdas264 0x1 0x6009001000006c00180d8000003000000000803000 rhs264 1
    topEColumns topETransposeColumns tree264 allowed264 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked264 checked264
    hw (he.trans rhsChecked264) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 265. -/
noncomputable def lambdas265 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000c00000002000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000020000000800000200000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000e00000400000000000000000000000020000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 265. -/
noncomputable def rhs265 : Nat := 0x1b480036d800006c000001b000009000db6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked265 : reconX topRColumns 0x6014002000000002406800c0010028003001000006 = rhs265 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 265. -/
theorem initialChecked265 : checkSearchInitial 8 180 12 rows265 lambdas265 0x41 0x6014002000000002406800c0010028003001000006 rhs265 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 265 has a listed outside support. -/
theorem complete265 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6014002000000002406800c0010028003001000006)
    (hweight : bitCount 180 (outsideMask word 0x6014002000000002406800c0010028003001000006) ≤ 1) :
    outsideMask word 0x6014002000000002406800c0010028003001000006 ∈ allowed265 := by
  exact outside_mem_of_search 8 180 12 rows265 lambdas265 0x41 0x6014002000000002406800c0010028003001000006 rhs265 1
    topEColumns topETransposeColumns tree265 allowed265 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked265 checked265
    hw (he.trans rhsChecked265) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 266. -/
noncomputable def lambdas266 : Nat := 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000800000a0000000100000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000e000002000000000000000000000000200000040000000000000000000000010e00000200000000000000000000000820000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 266. -/
noncomputable def rhs266 : Nat := 0x1b480024fc000048000001b00001200092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked266 : reconX topRColumns 0x6022004000000004806400c0008030003002000005 = rhs266 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 266. -/
theorem initialChecked266 : checkSearchInitial 8 180 15 rows266 lambdas266 0x2 0x6022004000000004806400c0008030003002000005 rhs266 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 266 has a listed outside support. -/
theorem complete266 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6022004000000004806400c0008030003002000005)
    (hweight : bitCount 180 (outsideMask word 0x6022004000000004806400c0008030003002000005) ≤ 1) :
    outsideMask word 0x6022004000000004806400c0008030003002000005 ∈ allowed266 := by
  exact outside_mem_of_search 8 180 15 rows266 lambdas266 0x2 0x6022004000000004806400c0008030003002000005 rhs266 1
    topEColumns topETransposeColumns tree266 allowed266 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked266 checked266
    hw (he.trans rhsChecked266) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 267. -/
noncomputable def lambdas267 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000c0000001000000200000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000038000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 267. -/
noncomputable def rhs267 : Nat := 0x1b48001248000048000001b00001b000db6000492

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked267 : reconX topRColumns 0x6030006000000002406800c0010000003003000006 = rhs267 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 267. -/
theorem initialChecked267 : checkSearchInitial 8 180 13 rows267 lambdas267 0x5 0x6030006000000002406800c0010000003003000006 rhs267 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 267 has a listed outside support. -/
theorem complete267 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6030006000000002406800c0010000003003000006)
    (hweight : bitCount 180 (outsideMask word 0x6030006000000002406800c0010000003003000006) ≤ 1) :
    outsideMask word 0x6030006000000002406800c0010000003003000006 ∈ allowed267 := by
  exact outside_mem_of_search 8 180 13 rows267 lambdas267 0x5 0x6030006000000002406800c0010000003003000006 rhs267 1
    topEColumns topETransposeColumns tree267 allowed267 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked267 checked267
    hw (he.trans rhsChecked267) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 268. -/
noncomputable def lambdas268 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000080000060000001100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000c00000400000030000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 268. -/
noncomputable def rhs268 : Nat := 0x1b4800006c000000000001b00002400092400049b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked268 : reconX topRColumns 0x604e008000000004806400c0008000003004000005 = rhs268 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 268. -/
theorem initialChecked268 : checkSearchInitial 8 180 14 rows268 lambdas268 0x40 0x604e008000000004806400c0008000003004000005 rhs268 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 268 has a listed outside support. -/
theorem complete268 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x604e008000000004806400c0008000003004000005)
    (hweight : bitCount 180 (outsideMask word 0x604e008000000004806400c0008000003004000005) ≤ 1) :
    outsideMask word 0x604e008000000004806400c0008000003004000005 ∈ allowed268 := by
  exact outside_mem_of_search 8 180 14 rows268 lambdas268 0x40 0x604e008000000004806400c0008000003004000005 rhs268 1
    topEColumns topETransposeColumns tree268 allowed268 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked268 checked268
    hw (he.trans rhsChecked268) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 269. -/
noncomputable def lambdas269 : Nat := 0x200000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000002000002010000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000020000020c0000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 269. -/
noncomputable def rhs269 : Nat := 0xb6d0004add8002d9000004800006c9000009024024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked269 : reconX topRColumns 0x60808000800000008202d005001800800640040000 = rhs269 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 269. -/
theorem initialChecked269 : checkSearchInitial 8 180 14 rows269 lambdas269 0x4 0x60808000800000008202d005001800800640040000 rhs269 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 269 has a listed outside support. -/
theorem complete269 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x60808000800000008202d005001800800640040000)
    (hweight : bitCount 180 (outsideMask word 0x60808000800000008202d005001800800640040000) ≤ 1) :
    outsideMask word 0x60808000800000008202d005001800800640040000 ∈ allowed269 := by
  exact outside_mem_of_search 8 180 14 rows269 lambdas269 0x4 0x60808000800000008202d005001800800640040000 rhs269 1
    topEColumns topETransposeColumns tree269 allowed269 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked269 checked269
    hw (he.trans rhsChecked269) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 270. -/
noncomputable def lambdas270 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000e00000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 270. -/
noncomputable def rhs270 : Nat := 0x48048001b6c00004800006db00003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked270 : reconX topRColumns 0x6181200380000000000000000036000006c01c0000 = rhs270 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 270. -/
theorem initialChecked270 : checkSearchInitial 8 180 13 rows270 lambdas270 0x40 0x6181200380000000000000000036000006c01c0000 rhs270 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 270 has a listed outside support. -/
theorem complete270 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6181200380000000000000000036000006c01c0000)
    (hweight : bitCount 180 (outsideMask word 0x6181200380000000000000000036000006c01c0000) ≤ 1) :
    outsideMask word 0x6181200380000000000000000036000006c01c0000 ∈ allowed270 := by
  exact outside_mem_of_search 8 180 13 rows270 lambdas270 0x40 0x6181200380000000000000000036000006c01c0000 rhs270 1
    topEColumns topETransposeColumns tree270 allowed270 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked270 checked270
    hw (he.trans rhsChecked270) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 271. -/
noncomputable def lambdas271 : Nat := (Nat.lor 0x1000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000800000000000000000000000000000e10000004000000000000000000000000000000000000000000000000000000000000000008000000000000000000000004000000000000000000000000000008200000000000020000000000000000000000000200000400000010000000000000000000000001 (Nat.shiftLeft 0x4000000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 271. -/
noncomputable def rhs271 : Nat := 0xb40000276000012000012000000240924000036900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked271 : reconX topRColumns 0x640040000000d801100a8018004002000200006000 = rhs271 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 271. -/
theorem initialChecked271 : checkSearchInitial 8 180 17 rows271 lambdas271 0x8 0x640040000000d801100a8018004002000200006000 rhs271 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 271 has a listed outside support. -/
theorem complete271 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x640040000000d801100a8018004002000200006000)
    (hweight : bitCount 180 (outsideMask word 0x640040000000d801100a8018004002000200006000) ≤ 1) :
    outsideMask word 0x640040000000d801100a8018004002000200006000 ∈ allowed271 := by
  exact outside_mem_of_search 8 180 17 rows271 lambdas271 0x8 0x640040000000d801100a8018004002000200006000 rhs271 1
    topEColumns topETransposeColumns tree271 allowed271 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked271 checked271
    hw (he.trans rhsChecked271) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 272. -/
noncomputable def lambdas272 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000006000004100000000000082000000000200000000400000000000000000000000000000000000000000000000000000400000000000021

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 272. -/
noncomputable def rhs272 : Nat := 0xb40000036000012000012000000240492000036900024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked272 : reconX topRColumns 0x640040000000fc01500a8010004002000200000000 = rhs272 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 272. -/
theorem initialChecked272 : checkSearchInitial 8 180 12 rows272 lambdas272 0x20 0x640040000000fc01500a8010004002000200000000 rhs272 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 272 has a listed outside support. -/
theorem complete272 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x640040000000fc01500a8010004002000200000000)
    (hweight : bitCount 180 (outsideMask word 0x640040000000fc01500a8010004002000200000000) ≤ 1) :
    outsideMask word 0x640040000000fc01500a8010004002000200000000 ∈ allowed272 := by
  exact outside_mem_of_search 8 180 12 rows272 lambdas272 0x20 0x640040000000fc01500a8010004002000200000000 rhs272 1
    topEColumns topETransposeColumns tree272 allowed272 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked272 checked272
    hw (he.trans rhsChecked272) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 273. -/
noncomputable def lambdas273 : Nat := 0x80000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000a0000002800000880000020000000100000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000200000e080000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 273. -/
noncomputable def rhs273 : Nat := 0xb6d00049b00002d9000004800006c0000009024024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked273 : reconX topRColumns 0x64008800800000008202d005001400800600040000 = rhs273 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 273. -/
theorem initialChecked273 : checkSearchInitial 8 180 16 rows273 lambdas273 0x10 0x64008800800000008202d005001400800600040000 rhs273 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 273 has a listed outside support. -/
theorem complete273 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x64008800800000008202d005001400800600040000)
    (hweight : bitCount 180 (outsideMask word 0x64008800800000008202d005001400800600040000) ≤ 1) :
    outsideMask word 0x64008800800000008202d005001400800600040000 ∈ allowed273 := by
  exact outside_mem_of_search 8 180 16 rows273 lambdas273 0x10 0x64008800800000008202d005001400800600040000 rhs273 1
    topEColumns topETransposeColumns tree273 allowed273 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked273 checked273
    hw (he.trans rhsChecked273) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 274. -/
noncomputable def lambdas274 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000e00000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 274. -/
noncomputable def rhs274 : Nat := 0x4b690001b6c00004800006d200003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked274 : reconX topRColumns 0x650128038000000000000000003a000006801c0000 = rhs274 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 274. -/
theorem initialChecked274 : checkSearchInitial 8 180 12 rows274 lambdas274 0x40 0x650128038000000000000000003a000006801c0000 rhs274 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 274 has a listed outside support. -/
theorem complete274 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x650128038000000000000000003a000006801c0000)
    (hweight : bitCount 180 (outsideMask word 0x650128038000000000000000003a000006801c0000) ≤ 1) :
    outsideMask word 0x650128038000000000000000003a000006801c0000 ∈ allowed274 := by
  exact outside_mem_of_search 8 180 12 rows274 lambdas274 0x40 0x650128038000000000000000003a000006801c0000 rhs274 1
    topEColumns topETransposeColumns tree274 allowed274 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked274 checked274
    hw (he.trans rhsChecked274) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 275. -/
noncomputable def lambdas275 : Nat := 0x20000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000040000000000000000000000000000003000000200000000000000000000000006000002080000000000104000000000200000000800000000000000000000000200000000000000000000000000000410000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 275. -/
noncomputable def rhs275 : Nat := 0xd80000fe400000000000900000048049200003fd80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked275 : reconX topRColumns 0x6800800000006c0088070028004001000400003000 = rhs275 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 275. -/
theorem initialChecked275 : checkSearchInitial 8 180 11 rows275 lambdas275 0x6 0x6800800000006c0088070028004001000400003000 rhs275 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 275 has a listed outside support. -/
theorem complete275 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6800800000006c0088070028004001000400003000)
    (hweight : bitCount 180 (outsideMask word 0x6800800000006c0088070028004001000400003000) ≤ 1) :
    outsideMask word 0x6800800000006c0088070028004001000400003000 ∈ allowed275 := by
  exact outside_mem_of_search 8 180 11 rows275 lambdas275 0x6 0x6800800000006c0088070028004001000400003000 rhs275 1
    topEColumns topETransposeColumns tree275 allowed275 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked275 checked275
    hw (he.trans rhsChecked275) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 276. -/
noncomputable def lambdas276 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000a0000020800000000001040000000001000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000c00000000000022

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 276. -/
noncomputable def rhs276 : Nat := 0xd800006e4000000000009000000480492000024d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked276 : reconX topRColumns 0x680080000000fc0188070008004001000400000000 = rhs276 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 276. -/
theorem initialChecked276 : checkSearchInitial 8 180 12 rows276 lambdas276 0x21 0x680080000000fc0188070008004001000400000000 rhs276 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 276 has a listed outside support. -/
theorem complete276 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x680080000000fc0188070008004001000400000000)
    (hweight : bitCount 180 (outsideMask word 0x680080000000fc0188070008004001000400000000) ≤ 1) :
    outsideMask word 0x680080000000fc0188070008004001000400000000 ∈ allowed276 := by
  exact outside_mem_of_search 8 180 12 rows276 lambdas276 0x21 0x680080000000fc0188070008004001000400000000 rhs276 1
    topEColumns topETransposeColumns tree276 allowed276 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked276 checked276
    hw (he.trans rhsChecked276) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 277. -/
noncomputable def lambdas277 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000e00000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 277. -/
noncomputable def rhs277 : Nat := 0x4a4d8001b4800004800006c900003f000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked277 : reconX topRColumns 0x688130038000000000000000003c000006401c0000 = rhs277 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 277. -/
theorem initialChecked277 : checkSearchInitial 8 180 12 rows277 lambdas277 0x40 0x688130038000000000000000003c000006401c0000 rhs277 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 277 has a listed outside support. -/
theorem complete277 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x688130038000000000000000003c000006401c0000)
    (hweight : bitCount 180 (outsideMask word 0x688130038000000000000000003c000006401c0000) ≤ 1) :
    outsideMask word 0x688130038000000000000000003c000006401c0000 ∈ allowed277 := by
  exact outside_mem_of_search 8 180 12 rows277 lambdas277 0x40 0x688130038000000000000000003c000006401c0000 rhs277 1
    topEColumns topETransposeColumns tree277 allowed277 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked277 checked277
    hw (he.trans rhsChecked277) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 278. -/
noncomputable def lambdas278 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000400000000000021000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 278. -/
noncomputable def rhs278 : Nat := 0x48049200001b480024d80000da4000036000012000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked278 : reconX topRColumns 0x6c01380a8002002000000400003000000c00080080 = rhs278 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 278. -/
theorem initialChecked278 : checkSearchInitial 8 180 11 rows278 lambdas278 0x10 0x6c01380a8002002000000400003000000c00080080 rhs278 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 278 has a listed outside support. -/
theorem complete278 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x6c01380a8002002000000400003000000c00080080)
    (hweight : bitCount 180 (outsideMask word 0x6c01380a8002002000000400003000000c00080080) ≤ 1) :
    outsideMask word 0x6c01380a8002002000000400003000000c00080080 ∈ allowed278 := by
  exact outside_mem_of_search 8 180 11 rows278 lambdas278 0x10 0x6c01380a8002002000000400003000000c00080080 rhs278 1
    topEColumns topETransposeColumns tree278 allowed278 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked278 checked278
    hw (he.trans rhsChecked278) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 279. -/
noncomputable def lambdas279 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 279. -/
noncomputable def rhs279 : Nat := 0x48048001b0000002400006ff00001b000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked279 : reconX topRColumns 0x7380200180000000000000000030006007c00c0000 = rhs279 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 279. -/
theorem initialChecked279 : checkSearchInitial 8 180 11 rows279 lambdas279 0x40 0x7380200180000000000000000030006007c00c0000 rhs279 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 279 has a listed outside support. -/
theorem complete279 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7380200180000000000000000030006007c00c0000)
    (hweight : bitCount 180 (outsideMask word 0x7380200180000000000000000030006007c00c0000) ≤ 1) :
    outsideMask word 0x7380200180000000000000000030006007c00c0000 ∈ allowed279 := by
  exact outside_mem_of_search 8 180 11 rows279 lambdas279 0x40 0x7380200180000000000000000030006007c00c0000 rhs279 1
    topEColumns topETransposeColumns tree279 allowed279 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked279 checked279
    hw (he.trans rhsChecked279) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 280. -/
noncomputable def lambdas280 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 280. -/
noncomputable def rhs280 : Nat := 0x48048002dd800002400006ff000012000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked280 : reconX topRColumns 0x738068010000000000000000003000a007c0080000 = rhs280 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 280. -/
theorem initialChecked280 : checkSearchInitial 8 180 11 rows280 lambdas280 0x40 0x738068010000000000000000003000a007c0080000 rhs280 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 280 has a listed outside support. -/
theorem complete280 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x738068010000000000000000003000a007c0080000)
    (hweight : bitCount 180 (outsideMask word 0x738068010000000000000000003000a007c0080000) ≤ 1) :
    outsideMask word 0x738068010000000000000000003000a007c0080000 ∈ allowed280 := by
  exact outside_mem_of_search 8 180 11 rows280 lambdas280 0x40 0x738068010000000000000000003000a007c0080000 rhs280 1
    topEColumns topETransposeColumns tree280 allowed280 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked280 checked280
    hw (he.trans rhsChecked280) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 281. -/
noncomputable def lambdas281 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 281. -/
noncomputable def rhs281 : Nat := 0x48048003f9000000000006ff000009000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked281 : reconX topRColumns 0x7380b0008000000000000000003000c007c0040000 = rhs281 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 281. -/
theorem initialChecked281 : checkSearchInitial 8 180 11 rows281 lambdas281 0x40 0x7380b0008000000000000000003000c007c0040000 rhs281 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 281 has a listed outside support. -/
theorem complete281 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7380b0008000000000000000003000c007c0040000)
    (hweight : bitCount 180 (outsideMask word 0x7380b0008000000000000000003000c007c0040000) ≤ 1) :
    outsideMask word 0x7380b0008000000000000000003000c007c0040000 ∈ allowed281 := by
  exact outside_mem_of_search 8 180 11 rows281 lambdas281 0x40 0x7380b0008000000000000000003000c007c0040000 rhs281 1
    topEColumns topETransposeColumns tree281 allowed281 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked281 checked281
    hw (he.trans rhsChecked281) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 282. -/
noncomputable def lambdas282 : Nat := 0x4000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000031000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 282. -/
noncomputable def rhs282 : Nat := 0x1b4920006d2000900000024fc0000000000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked282 : reconX topRColumns 0x7c09c00000000000009000c0018020004e00000000 = rhs282 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 282. -/
theorem initialChecked282 : checkSearchInitial 8 180 10 rows282 lambdas282 0x40 0x7c09c00000000000009000c0018020004e00000000 rhs282 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 282 has a listed outside support. -/
theorem complete282 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x7c09c00000000000009000c0018020004e00000000)
    (hweight : bitCount 180 (outsideMask word 0x7c09c00000000000009000c0018020004e00000000) ≤ 1) :
    outsideMask word 0x7c09c00000000000009000c0018020004e00000000 ∈ allowed282 := by
  exact outside_mem_of_search 8 180 10 rows282 lambdas282 0x40 0x7c09c00000000000009000c0018020004e00000000 rhs282 1
    topEColumns topETransposeColumns tree282 allowed282 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked282 checked282
    hw (he.trans rhsChecked282) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 283. -/
noncomputable def lambdas283 : Nat := (Nat.lor 0x1000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000004000002000000200000200000000000000000020000000000000000000000000200000400000020000020000000000000000001 (Nat.shiftLeft 0x2000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 283. -/
noncomputable def rhs283 : Nat := 0x6c00009000009000000240120120006db000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked283 : reconX topRColumns 0x8008000000030c09008c001802002000400001b000 = rhs283 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 283. -/
theorem initialChecked283 : checkSearchInitial 8 180 17 rows283 lambdas283 0x2 0x8008000000030c09008c001802002000400001b000 rhs283 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 283 has a listed outside support. -/
theorem complete283 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8008000000030c09008c001802002000400001b000)
    (hweight : bitCount 180 (outsideMask word 0x8008000000030c09008c001802002000400001b000) ≤ 1) :
    outsideMask word 0x8008000000030c09008c001802002000400001b000 ∈ allowed283 := by
  exact outside_mem_of_search 8 180 17 rows283 lambdas283 0x2 0x8008000000030c09008c001802002000400001b000 rhs283 1
    topEColumns topETransposeColumns tree283 allowed283 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked283 checked283
    hw (he.trans rhsChecked283) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 284. -/
noncomputable def lambdas284 : Nat := 0x200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000a000008000008200000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000004000002000000200000200000000000000000020000000000000000000400000400000400000020000020000820000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 284. -/
noncomputable def rhs284 : Nat := 0x480000900000900000024012da40006db000012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked284 : reconX topRColumns 0x8008000000032809408c001002002000400001d000 = rhs284 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 284. -/
theorem initialChecked284 : checkSearchInitial 8 180 16 rows284 lambdas284 0x12 0x8008000000032809408c001002002000400001d000 rhs284 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 284 has a listed outside support. -/
theorem complete284 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8008000000032809408c001002002000400001d000)
    (hweight : bitCount 180 (outsideMask word 0x8008000000032809408c001002002000400001d000) ≤ 1) :
    outsideMask word 0x8008000000032809408c001002002000400001d000 ∈ allowed284 := by
  exact outside_mem_of_search 8 180 16 rows284 lambdas284 0x12 0x8008000000032809408c001002002000400001d000 rhs284 1
    topEColumns topETransposeColumns tree284 allowed284 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked284 checked284
    hw (he.trans rhsChecked284) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 285. -/
noncomputable def lambdas285 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000a000008000008200000000000000000020000000000000000000000000000000000000000000000000000000000000000080000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 285. -/
noncomputable def rhs285 : Nat := 0xd80000900000024012480000ff600001b

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked285 : reconX topRColumns 0x800800000003600d40840000030020004000018005 = rhs285 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 285. -/
theorem initialChecked285 : checkSearchInitial 8 180 16 rows285 lambdas285 0x2 0x800800000003600d40840000030020004000018005 rhs285 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 285 has a listed outside support. -/
theorem complete285 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x800800000003600d40840000030020004000018005)
    (hweight : bitCount 180 (outsideMask word 0x800800000003600d40840000030020004000018005) ≤ 1) :
    outsideMask word 0x800800000003600d40840000030020004000018005 ∈ allowed285 := by
  exact outside_mem_of_search 8 180 16 rows285 lambdas285 0x2 0x800800000003600d40840000030020004000018005 rhs285 1
    topEColumns topETransposeColumns tree285 allowed285 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked285 checked285
    hw (he.trans rhsChecked285) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 286. -/
noncomputable def lambdas286 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000020000000c000006020000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000200000008000006000000110000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000410000000000020a00000020000020100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000400000010000020000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 286. -/
noncomputable def rhs286 : Nat := 0x36d8001b6c000001b000936000000900000900

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked286 : reconX topRColumns 0x86810c020004000000000000003a000c0980020020 = rhs286 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 286. -/
theorem initialChecked286 : checkSearchInitial 8 180 15 rows286 lambdas286 0x408 0x86810c020004000000000000003a000c0980020020 rhs286 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 286 has a listed outside support. -/
theorem complete286 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x86810c020004000000000000003a000c0980020020)
    (hweight : bitCount 180 (outsideMask word 0x86810c020004000000000000003a000c0980020020) ≤ 1) :
    outsideMask word 0x86810c020004000000000000003a000c0980020020 ∈ allowed286 := by
  exact outside_mem_of_search 8 180 15 rows286 lambdas286 0x408 0x86810c020004000000000000003a000c0980020020 rhs286 1
    topEColumns topETransposeColumns tree286 allowed286 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked286 checked286
    hw (he.trans rhsChecked286) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 287. -/
noncomputable def lambdas287 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000c4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000200000000000004400000000000000000000000000000000000000000000000000c00000010000030000020100000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 287. -/
noncomputable def rhs287 : Nat := 0x1248001b48000001b000924000000900000900

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked287 : reconX topRColumns 0x8f811c0200040000000000000030000c0900020020 = rhs287 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 287. -/
theorem initialChecked287 : checkSearchInitial 8 180 12 rows287 lambdas287 0x108 0x8f811c0200040000000000000030000c0900020020 rhs287 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 287 has a listed outside support. -/
theorem complete287 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0x8f811c0200040000000000000030000c0900020020)
    (hweight : bitCount 180 (outsideMask word 0x8f811c0200040000000000000030000c0900020020) ≤ 1) :
    outsideMask word 0x8f811c0200040000000000000030000c0900020020 ∈ allowed287 := by
  exact outside_mem_of_search 8 180 12 rows287 lambdas287 0x108 0x8f811c0200040000000000000030000c0900020020 rhs287 1
    topEColumns topETransposeColumns tree287 allowed287 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked287 checked287
    hw (he.trans rhsChecked287) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 288. -/
noncomputable def lambdas288 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000010000000400000e00000021000000000000000000000000000000000000000000000000000000040000000000002100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000400000000000000000c000000200000200000000800000000000000000000000000000000000000000000000000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 288. -/
noncomputable def rhs288 : Nat := 0x480db6000009240024d80000000000036000012000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked288 : reconX topRColumns 0xa600980a8002002000000400005600000100080080 = rhs288 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 288. -/
theorem initialChecked288 : checkSearchInitial 8 180 15 rows288 lambdas288 0x80 0xa600980a8002002000000400005600000100080080 rhs288 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 288 has a listed outside support. -/
theorem complete288 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xa600980a8002002000000400005600000100080080)
    (hweight : bitCount 180 (outsideMask word 0xa600980a8002002000000400005600000100080080) ≤ 1) :
    outsideMask word 0xa600980a8002002000000400005600000100080080 ∈ allowed288 := by
  exact outside_mem_of_search 8 180 15 rows288 lambdas288 0x80 0xa600980a8002002000000400005600000100080080 rhs288 1
    topEColumns topETransposeColumns tree288 allowed288 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked288 checked288
    hw (he.trans rhsChecked288) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 289. -/
noncomputable def lambdas289 : Nat := (Nat.lor 0x40000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000040000000000002800000080000080400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000002 (Nat.shiftLeft 0x80000000000000000000000000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 289. -/
noncomputable def rhs289 : Nat := 0x900db600002dd800006c0000d80000036000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked289 : reconX topRColumns 0xb40028108004004000000800005000a00c00180100 = rhs289 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 289. -/
theorem initialChecked289 : checkSearchInitial 8 180 17 rows289 lambdas289 0x20 0xb40028108004004000000800005000a00c00180100 rhs289 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 289 has a listed outside support. -/
theorem complete289 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xb40028108004004000000800005000a00c00180100)
    (hweight : bitCount 180 (outsideMask word 0xb40028108004004000000800005000a00c00180100) ≤ 1) :
    outsideMask word 0xb40028108004004000000800005000a00c00180100 ∈ allowed289 := by
  exact outside_mem_of_search 8 180 17 rows289 lambdas289 0x20 0xb40028108004004000000800005000a00c00180100 rhs289 1
    topEColumns topETransposeColumns tree289 allowed289 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked289 checked289
    hw (he.trans rhsChecked289) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 290. -/
noncomputable def lambdas290 : Nat := 0xc400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 290. -/
noncomputable def rhs290 : Nat := 0x4b69000124800006c0000ff6000024000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked290 : reconX topRColumns 0xe700d0020000000000000000000c00600f80100000 = rhs290 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 290. -/
theorem initialChecked290 : checkSearchInitial 8 180 11 rows290 lambdas290 0x400 0xe700d0020000000000000000000c00600f80100000 rhs290 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 290 has a listed outside support. -/
theorem complete290 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xe700d0020000000000000000000c00600f80100000)
    (hweight : bitCount 180 (outsideMask word 0xe700d0020000000000000000000c00600f80100000) ≤ 1) :
    outsideMask word 0xe700d0020000000000000000000c00600f80100000 ∈ allowed290 := by
  exact outside_mem_of_search 8 180 11 rows290 lambdas290 0x400 0xe700d0020000000000000000000c00600f80100000 rhs290 1
    topEColumns topETransposeColumns tree290 allowed290 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked290 checked290
    hw (he.trans rhsChecked290) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 291. -/
noncomputable def lambdas291 : Nat := 0xc400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 291. -/
noncomputable def rhs291 : Nat := 0x4b6900036d80000240000ff6000012000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked291 : reconX topRColumns 0xe70160010000000000000000000c00a00f80080000 = rhs291 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 291. -/
theorem initialChecked291 : checkSearchInitial 8 180 11 rows291 lambdas291 0x400 0xe70160010000000000000000000c00a00f80080000 rhs291 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 291 has a listed outside support. -/
theorem complete291 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xe70160010000000000000000000c00a00f80080000)
    (hweight : bitCount 180 (outsideMask word 0xe70160010000000000000000000c00a00f80080000) ≤ 1) :
    outsideMask word 0xe70160010000000000000000000c00a00f80080000 ∈ allowed291 := by
  exact outside_mem_of_search 8 180 11 rows291 lambdas291 0x400 0xe70160010000000000000000000c00a00f80080000 rhs291 1
    topEColumns topETransposeColumns tree291 allowed291 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked291 checked291
    hw (he.trans rhsChecked291) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 292. -/
noncomputable def lambdas292 : Nat := 0x800000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000200000020000030000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000280000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 292. -/
noncomputable def rhs292 : Nat := 0xb40000da400002400002d000000480db6000036d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked292 : reconX topRColumns 0xe80080000000240128168020000005000400006000 = rhs292 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 292. -/
theorem initialChecked292 : checkSearchInitial 8 180 14 rows292 lambdas292 0x40 0xe80080000000240128168020000005000400006000 rhs292 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 292 has a listed outside support. -/
theorem complete292 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xe80080000000240128168020000005000400006000)
    (hweight : bitCount 180 (outsideMask word 0xe80080000000240128168020000005000400006000) ≤ 1) :
    outsideMask word 0xe80080000000240128168020000005000400006000 ∈ allowed292 := by
  exact outside_mem_of_search 8 180 14 rows292 lambdas292 0x40 0xe80080000000240128168020000005000400006000 rhs292 1
    topEColumns topETransposeColumns tree292 allowed292 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked292 checked292
    hw (he.trans rhsChecked292) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 293. -/
noncomputable def lambdas293 : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000020000000000003000000040000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000002800000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 293. -/
noncomputable def rhs293 : Nat := 0xb40000da4000900000024000000480db6480036d80036

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked293 : reconX topRColumns 0xe80400080000240128168020000000000400406000 = rhs293 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 293. -/
theorem initialChecked293 : checkSearchInitial 8 180 14 rows293 lambdas293 0x20 0xe80400080000240128168020000000000400406000 rhs293 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 293 has a listed outside support. -/
theorem complete293 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xe80400080000240128168020000000000400406000)
    (hweight : bitCount 180 (outsideMask word 0xe80400080000240128168020000000000400406000) ≤ 1) :
    outsideMask word 0xe80400080000240128168020000000000400406000 ∈ allowed293 := by
  exact outside_mem_of_search 8 180 14 rows293 lambdas293 0x20 0xe80400080000240128168020000000000400406000 rhs293 1
    topEColumns topETransposeColumns tree293 allowed293 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked293 checked293
    hw (he.trans rhsChecked293) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 294. -/
noncomputable def lambdas294 : Nat := 0xc400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 294. -/
noncomputable def rhs294 : Nat := 0x492000036fc0000480000fe4000036000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked294 : reconX topRColumns 0xee0050030000000000000000000600c00f00180000 = rhs294 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 294. -/
theorem initialChecked294 : checkSearchInitial 8 180 11 rows294 lambdas294 0x400 0xee0050030000000000000000000600c00f00180000 rhs294 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 294 has a listed outside support. -/
theorem complete294 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xee0050030000000000000000000600c00f00180000)
    (hweight : bitCount 180 (outsideMask word 0xee0050030000000000000000000600c00f00180000) ≤ 1) :
    outsideMask word 0xee0050030000000000000000000600c00f00180000 ∈ allowed294 := by
  exact outside_mem_of_search 8 180 11 rows294 lambdas294 0x400 0xee0050030000000000000000000600c00f00180000 rhs294 1
    topEColumns topETransposeColumns tree294 allowed294 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked294 checked294
    hw (he.trans rhsChecked294) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 295. -/
noncomputable def lambdas295 : Nat := 0xc400000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 295. -/
noncomputable def rhs295 : Nat := 0x492000024b400006c0000fe400002d000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked295 : reconX topRColumns 0xee0088028000000000000000000600a00f00140000 = rhs295 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 295. -/
theorem initialChecked295 : checkSearchInitial 8 180 11 rows295 lambdas295 0x400 0xee0088028000000000000000000600a00f00140000 rhs295 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 295 has a listed outside support. -/
theorem complete295 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xee0088028000000000000000000600a00f00140000)
    (hweight : bitCount 180 (outsideMask word 0xee0088028000000000000000000600a00f00140000) ≤ 1) :
    outsideMask word 0xee0088028000000000000000000600a00f00140000 ∈ allowed295 := by
  exact outside_mem_of_search 8 180 11 rows295 lambdas295 0x400 0xee0088028000000000000000000600a00f00140000 rhs295 1
    topEColumns topETransposeColumns tree295 allowed295 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked295 checked295
    hw (he.trans rhsChecked295) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 296. -/
noncomputable def lambdas296 : Nat := 0xc40000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 296. -/
noncomputable def rhs296 : Nat := 0x492000036fc0000240000fe4000012000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked296 : reconX topRColumns 0xee0170010000000000000000000600a00f00080000 = rhs296 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 296. -/
theorem initialChecked296 : checkSearchInitial 8 180 10 rows296 lambdas296 0x200 0xee0170010000000000000000000600a00f00080000 rhs296 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 296 has a listed outside support. -/
theorem complete296 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xee0170010000000000000000000600a00f00080000)
    (hweight : bitCount 180 (outsideMask word 0xee0170010000000000000000000600a00f00080000) ≤ 1) :
    outsideMask word 0xee0170010000000000000000000600a00f00080000 ∈ allowed296 := by
  exact outside_mem_of_search 8 180 10 rows296 lambdas296 0x200 0xee0170010000000000000000000600a00f00080000 rhs296 1
    topEColumns topETransposeColumns tree296 allowed296 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked296 checked296
    hw (he.trans rhsChecked296) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 297. -/
noncomputable def lambdas297 : Nat := 0xc40000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 297. -/
noncomputable def rhs297 : Nat := 0x492000024b40000000000fe4000009000000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked297 : reconX topRColumns 0xee01a8008000000000000000000600c00f00040000 = rhs297 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 297. -/
theorem initialChecked297 : checkSearchInitial 8 180 10 rows297 lambdas297 0x200 0xee01a8008000000000000000000600c00f00040000 rhs297 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 297 has a listed outside support. -/
theorem complete297 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xee01a8008000000000000000000600c00f00040000)
    (hweight : bitCount 180 (outsideMask word 0xee01a8008000000000000000000600c00f00040000) ≤ 1) :
    outsideMask word 0xee01a8008000000000000000000600c00f00040000 ∈ allowed297 := by
  exact outside_mem_of_search 8 180 10 rows297 lambdas297 0x200 0xee01a8008000000000000000000600c00f00040000 rhs297 1
    topEColumns topETransposeColumns tree297 allowed297 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked297 checked297
    hw (he.trans rhsChecked297) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 298. -/
noncomputable def lambdas298 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c40000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000800000018000011000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000004000000000000000000000000000000300000020000000000000000000000000000000018000000000000000000000000000000100000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 298. -/
noncomputable def rhs298 : Nat := 0x6c000048000000000001b00000090049200001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked298 : reconX topRColumns 0xf001000000006c00180d8000000003000800003000 = rhs298 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 298. -/
theorem initialChecked298 : checkSearchInitial 8 180 10 rows298 lambdas298 0x42 0xf001000000006c00180d8000000003000800003000 rhs298 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 298 has a listed outside support. -/
theorem complete298 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xf001000000006c00180d8000000003000800003000)
    (hweight : bitCount 180 (outsideMask word 0xf001000000006c00180d8000000003000800003000) ≤ 1) :
    outsideMask word 0xf001000000006c00180d8000000003000800003000 ∈ allowed298 := by
  exact outside_mem_of_search 8 180 10 rows298 lambdas298 0x42 0xf001000000006c00180d8000000003000800003000 rhs298 1
    topEColumns topETransposeColumns tree298 allowed298 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked298 checked298
    hw (he.trans rhsChecked298) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 299. -/
noncomputable def lambdas299 : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000c400000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000080000000000001100000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000400000000000000000000000000000030000002000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 299. -/
noncomputable def rhs299 : Nat := 0x6c000048000000000000000000090049290001b480012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked299 : reconX topRColumns 0xf008001000006c00180d8000000000000800803000 = rhs299 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 299. -/
theorem initialChecked299 : checkSearchInitial 8 180 11 rows299 lambdas299 0x81 0xf008001000006c00180d8000000000000800803000 rhs299 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 299 has a listed outside support. -/
theorem complete299 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xf008001000006c00180d8000000000000800803000)
    (hweight : bitCount 180 (outsideMask word 0xf008001000006c00180d8000000000000800803000) ≤ 1) :
    outsideMask word 0xf008001000006c00180d8000000000000800803000 ∈ allowed299 := by
  exact outside_mem_of_search 8 180 11 rows299 lambdas299 0x81 0xf008001000006c00180d8000000000000800803000 rhs299 1
    topEColumns topETransposeColumns tree299 allowed299 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked299 checked299
    hw (he.trans rhsChecked299) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 300. -/
noncomputable def lambdas300 : Nat := 0x400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000003100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000800000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 300. -/
noncomputable def rhs300 : Nat := 0x90049200003690000048000090000002d000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked300 : reconX topRColumns 0xfc0070110004004000000800000000c00800140100 = rhs300 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 300. -/
theorem initialChecked300 : checkSearchInitial 8 180 12 rows300 lambdas300 0x100 0xfc0070110004004000000800000000c00800140100 rhs300 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 300 has a listed outside support. -/
theorem complete300 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc0070110004004000000800000000c00800140100)
    (hweight : bitCount 180 (outsideMask word 0xfc0070110004004000000800000000c00800140100) ≤ 1) :
    outsideMask word 0xfc0070110004004000000800000000c00800140100 ∈ allowed300 := by
  exact outside_mem_of_search 8 180 12 rows300 lambdas300 0x100 0xfc0070110004004000000800000000c00800140100 rhs300 1
    topEColumns topETransposeColumns tree300 allowed300 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked300 checked300
    hw (he.trans rhsChecked300) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 301. -/
noncomputable def lambdas301 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 301. -/
noncomputable def rhs301 : Nat := 0x900492000000480000240000900000000000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked301 : reconX topRColumns 0xfc0118138004004000000800000000600800000100 = rhs301 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 301. -/
theorem initialChecked301 : checkSearchInitial 8 180 11 rows301 lambdas301 0x80 0xfc0118138004004000000800000000600800000100 rhs301 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 301 has a listed outside support. -/
theorem complete301 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc0118138004004000000800000000600800000100)
    (hweight : bitCount 180 (outsideMask word 0xfc0118138004004000000800000000600800000100) ≤ 1) :
    outsideMask word 0xfc0118138004004000000800000000600800000100 ∈ allowed301 := by
  exact outside_mem_of_search 8 180 11 rows301 lambdas301 0x80 0xfc0118138004004000000800000000600800000100 rhs301 1
    topEColumns topETransposeColumns tree301 allowed301 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked301 checked301
    hw (he.trans rhsChecked301) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 302. -/
noncomputable def lambdas302 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000800000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 302. -/
noncomputable def rhs302 : Nat := 0x900492000036900000240000900000009000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked302 : reconX topRColumns 0xfc0150130004004000000800000000a00800040100 = rhs302 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 302. -/
theorem initialChecked302 : checkSearchInitial 8 180 11 rows302 lambdas302 0x80 0xfc0150130004004000000800000000a00800040100 rhs302 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 302 has a listed outside support. -/
theorem complete302 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc0150130004004000000800000000a00800040100)
    (hweight : bitCount 180 (outsideMask word 0xfc0150130004004000000800000000a00800040100) ≤ 1) :
    outsideMask word 0xfc0150130004004000000800000000a00800040100 ∈ allowed302 := by
  exact outside_mem_of_search 8 180 11 rows302 lambdas302 0x80 0xfc0150130004004000000800000000a00800040100 rhs302 1
    topEColumns topETransposeColumns tree302 allowed302 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked302 checked302
    hw (he.trans rhsChecked302) hweight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual row witnesses for affine search fiber 303. -/
noncomputable def lambdas303 : Nat := 0x40000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000800000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The exact right-hand side of affine search fiber 303. -/
noncomputable def rhs303 : Nat := 0x900492000024d80000000000900000012000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The canonical carry map gives the stated right-hand side. -/
theorem rhsChecked303 : reconX topRColumns 0xfc0188128004004000000800000000c00800080100 = rhs303 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every initial dual row of affine search fiber 303. -/
theorem initialChecked303 : checkSearchInitial 8 180 11 rows303 lambdas303 0x80 0xfc0188128004004000000800000000c00800080100 rhs303 topETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of affine search fiber 303 has a listed outside support. -/
theorem complete303 {word : Nat} (hw : word < 2^180)
    (he : reconX topEColumns word = reconX topRColumns 0xfc0188128004004000000800000000c00800080100)
    (hweight : bitCount 180 (outsideMask word 0xfc0188128004004000000800000000c00800080100) ≤ 1) :
    outsideMask word 0xfc0188128004004000000800000000c00800080100 ∈ allowed303 := by
  exact outside_mem_of_search 8 180 11 rows303 lambdas303 0x80 0xfc0188128004004000000800000000c00800080100 rhs303 1
    topEColumns topETransposeColumns tree303 allowed303 (by decide)
    (fun lam v _ _ => topETranspose_parityFold lam v) topTranspose_bounded initialChecked303 checked303
    hw (he.trans rhsChecked303) hweight

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_highcap_search.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomHighSearchSupport
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart10

noncomputable section
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch
open F2Mask PackedDigits FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 463. -/
noncomputable def rows463 : Nat := (Nat.lor 0x18c28805a1024610cd0246500000000000000000000000000000000000000000040000006001000000040040000000000000000000000000000000000000000002000000a000800000020020000000000000000000000000000000000000000001000000c0004000000100100000000000000000000000000000000000000000008000000c0120000000800000000000000000000000000000000000000000003542b880a500c013814e000000000000000000000000000000000000000000003082b810a9000a12854e60000000000000000000000000000000000000000000001000000180240000001000000000000000000000000000000000000000000005080c80018002014006c800000000000000000000000000000000000000000000040c1000040e001e86cd0000000000000000000000000000000000000000000002000000300480000002000000000000000000000000000000000000000000201480018050021005800340000000000000000000000000000000000000000000c080100066002012c00d000000000000000000000000000000000000000000000040000006009000000040000000000000000000000000000000000000000010d6a801a1064618c84a5960000000000000000000000000000000000000000030c0180001004620cd825b1 (Nat.shiftLeft 0x1800080000010012000000000000000000000000000000000000000000000000280004000000800900000000000000000000000000000000000000000000000003000100000020024000000000000000000000000000000000000000000000000600004000000800900000000000000000000000000000000000000000000000000c000400000080090000000000000000000000000000000000000000000000001800010000002002400000000000000000000000000000000000000000000000028000400000080090000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c0000800000100120000000000000000000000000000000000000000000000000c0004000000800900000000000000000000000000000000000000000000000014000200000040048000000000000000000000000000000000000000000000001800010000002002400000000000000000000000000000000000000000010000005000000000010012 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 463. -/
noncomputable def lambdas463 : Nat := (Nat.lor 0x8c2840c0000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000a02c400000000000000400000000000000000000000000000000000000000000842c40000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000002000c000000000000000800000000000000000000000000000000000000000000e00c10000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000a0004000000000000010000000000000000000000000000000000000000000020001800000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000008ca84340000000000000020000000000000000000000000000000000000000008c00430000000000000001 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 463. -/
noncomputable def allowed463 : List Nat := [0x40000000001,0x1000000000000004000001]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 463. -/
noncomputable def tree463 : ParitySearchTree := (.split 13 (.pack [22,13,6]) (.split 14 (.split 2 (.pack [2,7]) (.split 44 (.pack [11,29]) (.split 57 (.pack [13,7]) (.split 58 (.pack [23,12]) (.split 86 (.split 24 (.pack [20]) (.split 27 (.pack [21]) (.split 39 (.pack [10]) (.split 66 (.pack [19]) (.split 85 (.pack [13]) (.zero 26)))))) (.zero 14)))))) (.split 15 (.split 12 (.pack [20,12]) (.split 27 (.pack [26,0]) (.split 54 (.pack [11,10]) (.split 73 (.split 18 (.pack [24]) (.split 20 (.pack [25]) (.split 28 (.pack [22]) (.split 29 (.pack [27]) (.split 32 (.pack [29]) (.split 42 (.pack [12]) (.split 43 (.pack [13]) (.split 52 (.pack [8]) (.split 57 (.pack [13]) (.split 59 (.pack [13]) (.split 67 (.pack [19]) (.split 71 (.pack [29]) (.split 72 (.pack [22]) (.split 75 (.pack [23]) (.split 77 (.pack [23]) (.split 82 (.pack [3]) (.split 84 (.pack [12]) (.split 86 (.pack [14]) (.split 88 (.pack [29]) (.split 89 (.pack [28]) (.zero 10))))))))))))))))))))) (.split 74 (.pack [22,2]) (.zero 21)))))) (.split 18 (.split 21 (.split 6 (.pack [3]) (.split 9 (.pack [20]) (.split 48 (.pack [5]) (.split 67 (.pack [19]) (.split 68 (.pack [18]) (.zero 17)))))) (.split 33 (.split 9 (.pack [17]) (.split 10 (.pack [18]) (.split 20 (.pack [25]) (.split 22 (.pack [18]) (.split 27 (.pack [21]) (.split 29 (.pack [27]) (.split 32 (.pack [29]) (.split 37 (.pack [7]) (.split 39 (.pack [26]) (.split 52 (.pack [8]) (.split 55 (.pack [22]) (.split 57 (.pack [13]) (.split 59 (.pack [13]) (.split 64 (.pack [6]) (.split 71 (.pack [29]) (.split 72 (.pack [22]) (.split 73 (.pack [21]) (.split 75 (.pack [23]) (.split 77 (.pack [23]) (.split 83 (.pack [11]) (.split 88 (.pack [29]) (.split 89 (.pack [28]) (.zero 9))))))))))))))))))))))) (.split 60 (.split 1 (.pack [13]) (.split 4 (.pack [6]) (.split 16 (.pack [22]) (.split 62 (.pack [25]) (.split 88 (.pack [29]) (.zero 16)))))) (.split 79 (.pack [25,3]) (.split 80 (.pack [8,3]) (.zero 24)))))) (.split 20 (.split 23 (.pack [19,9]) (.split 35 (.pack [2,5]) (.split 62 (.split 1 (.pack [13]) (.split 4 (.pack [3]) (.split 16 (.pack [22]) (.split 60 (.pack [24]) (.split 88 (.pack [29]) (.zero 16)))))) (.split 78 (.split 4 (.pack [16]) (.split 6 (.pack [17]) (.split 7 (.pack [18]) (.split 10 (.pack [18]) (.split 11 (.pack [19]) (.split 19 (.pack [23]) (.split 21 (.pack [17]) (.split 22 (.pack [18]) (.split 24 (.pack [20]) (.split 37 (.pack [7]) (.split 38 (.pack [5]) (.split 39 (.pack [26]) (.split 46 (.pack [2]) (.split 64 (.pack [3]) (.split 70 (.pack [20]) (.split 71 (.pack [20]) (.zero 6))))))))))))))))) (.split 79 (.pack [24,7]) (.zero 25)))))) (.split 27 (.pack [21,26,0]) (.split 28 (.split 16 (.pack [23,16]) (.split 55 (.pack [11,28]) (.split 72 (.split 31 (.pack [23]) (.split 43 (.pack [13]) (.split 70 (.pack [20]) (.split 87 (.pack [29]) (.split 89 (.pack [7]) (.zero 28)))))) (.split 74 (.pack [21,2]) (.zero 22))))) (.split 29 (.split 26 (.split 32 (.pack [2]) (.split 44 (.pack [14]) (.split 71 (.pack [20]) (.split 87 (.pack [28]) (.split 88 (.pack [16]) (.zero 29)))))) (.split 41 (.pack [8,11]) (.split 68 (.pack [18,17]) (.split 84 (.pack [12,29]) (.split 85 (.pack [13,26]) (.zero 27)))))) (.split 32 (.split 44 (.pack [14,11]) (.split 71 (.pack [20,2]) (.split 87 (.pack [28,2]) (.split 88 (.pack [16,2]) (.zero 29))))) (.split 42 (.split 0 (.split 1 (.pack [13]) (.split 2 (.pack [2]) (.split 4 (.pack [16]) (.split 5 (.pack [5]) (.split 6 (.pack [17]) (.split 7 (.pack [18]) (.split 8 (.pack [19]) (.split 9 (.pack [17]) (.split 10 (.pack [18]) (.split 11 (.pack [19]) (.split 12 (.pack [21]) (.split 16 (.pack [22]) (.split 19 (.pack [23]) (.split 21 (.pack [17]) (.split 22 (.pack [18]) (.split 23 (.pack [19]) (.split 24 (.pack [20]) (.split 26 (.pack [27]) (.split 31 (.pack [23]) (.split 33 (.pack [24]) (.split 35 (.pack [2]) (.split 37 (.pack [6]) (.split 38 (.pack [5]) (.split 39 (.pack [26]) (.split 41 (.pack [8]) (.split 43 (.pack [13]) (.split 44 (.pack [11]) (.split 45 (.pack [2]) (.split 46 (.pack [2]) (.split 48 (.pack [17]) (.split 49 (.pack [5]) (.split 50 (.pack [19]) (.split 51 (.pack [20]) (.split 52 (.pack [8]) (.split 54 (.pack [21]) (.split 55 (.pack [11]) (.split 57 (.pack [13]) (.split 58 (.pack [14]) (.split 59 (.pack [12]) (.split 60 (.pack [24]) (.split 62 (.pack [16]) (.split 64 (.pack [6]) (.split 66 (.pack [19]) (.split 67 (.zero 19) (.split 68 (.zero 17) (.split 70 (.pack [20]) (.split 71 (.zero 20) (.split 72 (.pack [22]) (.split 73 (.pack [21]) (.split 74 (.zero 2) (.split 75 (.pack [23]) (.split 77 (.zero 5) (.split 78 (.zero 6) (.split 79 (.zero 25) (.split 80 (.zero 8) (.split 82 (.pack [3]) (.split 83 (.zero 3) (.split 84 (.zero 12) (.split 85 (.zero 13) (.split 86 (.zero 7) (.split 87 (.pack [15]) (.split 88 (.zero 1) (.split 89 (.zero 0) .done))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.split 12 (.pack [21,20]) (.split 58 (.pack [14,23]) (.split 59 (.pack [13,4]) (.split 84 (.pack [27,10]) (.zero 12)))))) (.split 43 (.split 1 (.pack [28,16]) (.split 57 (.pack [14,28]) (.split 59 (.pack [12,28]) (.split 85 (.pack [27,26]) (.zero 13))))) (.split 52 (.split 8 (.pack [19,9]) (.split 38 (.pack [5,7]) (.split 41 (.pack [27,11]) (.split 51 (.split 9 (.pack [17]) (.split 12 (.pack [21]) (.split 24 (.pack [26]) (.split 70 (.pack [28]) (.split 71 (.pack [29]) (.zero 20)))))) (.split 80 (.pack [24,9]) (.zero 8)))))) (.split 54 (.split 12 (.pack [12,20]) (.split 73 (.pack [11,10]) (.split 74 (.pack [22,2]) (.zero 21)))) (.split 57 (.split 1 (.pack [14,16]) (.split 59 (.pack [12,4]) (.split 85 (.pack [27,14]) (.zero 13)))) (.split 59 (.pack [13,12,4]) (.split 67 (.split 8 (.pack [8,17]) (.split 11 (.pack [11,17]) (.split 23 (.pack [25,17]) (.split 50 (.pack [17,7]) (.split 66 (.pack [26,17]) (.zero 19)))))) (.split 71 (.split 44 (.pack [14,11]) (.split 87 (.split 31 (.pack [20]) (.split 70 (.pack [9]) (.split 89 (.pack [20]) (.zero 28)))) (.split 88 (.pack [16,20]) (.zero 29)))) (.split 72 (.split 16 (.pack [23,16]) (.split 55 (.split 11 (.pack [19]) (.split 41 (.pack [8]) (.split 44 (.pack [29]) (.split 83 (.pack [9]) (.zero 11))))) (.split 74 (.pack [21,2]) (.zero 22)))) (.split 73 (.split 12 (.pack [12,20]) (.split 74 (.pack [22,2]) (.zero 21))) (.split 75 (.split 16 (.pack [22,16]) (.split 19 (.split 9 (.pack [17]) (.split 10 (.pack [18]) (.split 22 (.pack [18]) (.split 37 (.pack [7]) (.split 39 (.pack [26]) (.split 55 (.pack [22]) (.split 64 (.pack [3]) (.split 77 (.pack [23]) (.split 83 (.pack [11]) (.split 88 (.pack [29]) (.split 89 (.pack [10]) (.zero 9)))))))))))) (.split 31 (.pack [28,3]) (.split 58 (.pack [12,14]) (.split 77 (.pack [5,10]) (.zero 23)))))) (.split 77 (.pack [23,5,9]) (.split 82 (.split 4 (.pack [16,6]) (.split 6 (.pack [17,0]) (.split 7 (.split 10 (.pack [9]) (.split 22 (.pack [7]) (.split 49 (.pack [5]) (.split 66 (.pack [19]) (.split 68 (.pack [17]) (.zero 18)))))) (.split 19 (.pack [23,4]) (.split 21 (.pack [17,24]) (.split 24 (.pack [20,26]) (.split 33 (.split 60 (.pack [16]) (.split 79 (.pack [25]) (.split 80 (.pack [8]) (.zero 24)))) (.split 45 (.pack [2,0]) (.split 46 (.pack [2,6]) (.split 49 (.pack [5,18]) (.split 50 (.pack [19,4]) (.split 64 (.split 10 (.pack [18]) (.split 11 (.pack [19]) (.split 22 (.pack [18]) (.split 23 (.pack [19]) (.split 37 (.pack [7]) (.split 38 (.pack [5]) (.split 39 (.pack [26]) (.split 70 (.pack [20]) (.split 78 (.pack [25]) (.zero 6)))))))))) (.split 83 (.pack [11,1]) (.zero 3)))))))))))))) (.split 84 (.split 0 (.split 26 .done (.split 41 (.pack [8]) (.split 68 (.pack [17]) (.split 85 (.pack [13]) (.zero 27))))) (.split 12 (.pack [21,20]) (.split 58 (.pack [23,14]) (.zero 12)))) (.split 86 (.pack [14,26,7]) (.split 88 (.pack [29,16,9]) (.split 89 (.split 31 (.pack [23,9]) (.split 70 (.pack [20,4]) (.split 87 (.pack [29,9]) (.zero 28)))) (.zero 10)))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 463 is kernel-checked. -/
theorem checked463 : checkParitySearch 8 (fun q => lane 256 q rows463) 0x402 (allowed463.contains) tree463 0x3fdefdd5edf7eebbdfdfff7 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 463 satisfy the full bottom equations. -/
theorem initial463 : checkSearchInitial 8 90 30 rows463 lambdas463 0x402 0x21022a120811442020008 0x8a8482009b6454241004db bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 463. -/
theorem rhs463 : reconX bottomRColumns 0x21022a120811442020008 = 0x8a8482009b6454241004db := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 463 has a listed outside support. -/
theorem complete463 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x21022a120811442020008)
    (hoff : bitCount 90 (outsideMask word 0x21022a120811442020008) ≤ 3) :
    outsideMask word 0x21022a120811442020008 ∈ allowed463 := by
  exact outside_mem_of_search 8 90 30 rows463 lambdas463 0x402 0x21022a120811442020008 0x8a8482009b6454241004db 3
    bottomEColumns bottomETransposeColumns tree463 allowed463 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial463 checked463
    hw (he.trans rhs463) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 464. -/
noncomputable def rows464 : Nat := (Nat.lor 0x28000400000080090000000000000000000000000000000000000000002000000300000000002002400000000000000000000000000000000000000000100000050000000000100120000000000000000000000000000000000000000008000006000000000008009000000000000000000000000000000000000000002e02840080010001009600600000000000000000000000000000000000000000008000000c012000000080000000000000000000000000000000000000000000304004201a000c048804a000000000000000000000000000000000000000000000100000018024000000100000000000000000000000000000000000000000000008000002801200000008000000000000000000000000000000000000000000000400000300090000000400000000000000000000000000000000000000000003ce00ac0028220226003400000000000000000000000000000000000000000003c080a8804824522e20370000000000000000000000000000000000000000000000800000600120000000800000000000000000000000000000000000000000000c402c000c0010084016c00000000000000000000000000000000000000000040020288001005400bc16e0000000000000000000000000000000000000000000001000000c00240000001 (Nat.shiftLeft 0x18000800000100120000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c00008000001001200000000000000000000000000000000000000000000000014000200000040048000000000000000000000000000000000000000000000001800010000002002400000000000000000000000000000000000000000000000003000100000020024000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c0000800000100120000000000000000000000000000000000000000000000000c00040000008009000000000000000000000000000000000000000000003000c40032020022406880 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 464. -/
noncomputable def lambdas464 : Nat := (Nat.lor 0x800000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000010010000800000000002000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000088008000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000004d000600000000000000200000000000000000000000000000000000000000004c200600000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000010002800000000000000400000000000000000000000000000000000000000000380288000000000000020000000000000000000000000000000000000000000000000000000000000001 (Nat.shiftLeft 0x10000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000004000c00000000000400000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 464. -/
noncomputable def allowed464 : List Nat := [0x900000000004000,0x12002000000,0x28000002000000000000,0x20400000000000000200,0x1000000000012000000000,0x20000000000000000024000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 464. -/
noncomputable def tree464 : ParitySearchTree := (.split 7 (.split 4 (.pack [7,13]) (.split 19 (.pack [7,23]) (.split 46 (.pack [0,7]) (.split 63 (.pack [7,24]) (.split 65 (.pack [7,1]) (.zero 15)))))) (.split 11 (.split 8 (.pack [8,2]) (.split 23 (.pack [10,2]) (.split 50 (.pack [3,10]) (.split 66 (.pack [10,25]) (.split 67 (.pack [10,26]) (.zero 17)))))) (.split 13 (.split 16 (.split 1 (.pack [11]) (.split 4 (.pack [15]) (.split 60 (.pack [22]) (.split 62 (.pack [12]) (.split 88 (.pack [27]) (.zero 13)))))) (.split 28 (.split 25 (.pack [16]) (.split 40 (.pack [7]) (.split 67 (.pack [17]) (.split 84 (.pack [16]) (.split 86 (.pack [25]) (.zero 26)))))) (.split 55 (.pack [10,9]) (.split 72 (.pack [0,21]) (.split 74 (.pack [19,11]) (.zero 20)))))) (.split 14 (.split 17 (.split 2 (.pack [9]) (.split 5 (.pack [11]) (.split 60 (.pack [22]) (.split 61 (.pack [23]) (.split 89 .done (.zero 14)))))) (.split 29 (.pack [27,5]) (.split 56 (.split 1 (.pack [13]) (.split 2 (.pack [14]) (.split 16 (.pack [20]) (.split 19 (.pack [15]) (.split 28 (.pack [20]) (.split 44 (.pack [10]) (.split 59 .done (.split 70 (.pack [18]) (.split 75 (.pack [3]) (.split 77 (.pack [1]) (.split 85 (.pack [25]) (.split 86 (.pack [25]) (.split 87 (.pack [27]) (.split 89 (.pack [14]) (.zero 11))))))))))))))) (.split 72 (.pack [20,0]) (.split 73 (.pack [19,11]) (.zero 21)))))) (.split 22 (.split 19 (.pack [15,11]) (.split 34 (.split 1 (.pack [13]) (.split 2 (.pack [14]) (.split 3 (.pack [3]) (.split 5 (.pack [14]) (.split 6 (.pack [6]) (.split 8 (.pack [17]) (.split 15 (.pack [12]) (.split 16 (.pack [20]) (.split 17 (.pack [14]) (.split 30 (.pack [0]) (.split 32 (.pack [27]) (.split 44 (.pack [10]) (.split 59 (.pack [11]) (.split 63 (.pack [15]) (.split 65 (.pack [15]) (.split 73 (.pack [21]) (.split 86 (.pack [26]) (.zero 1)))))))))))))))))) (.split 61 (.pack [12,14]) (.split 78 (.split 6 (.pack [1]) (.split 36 (.pack [3]) (.split 39 (.pack [25]) (.split 52 (.pack [8]) (.split 53 (.pack [7]) (.zero 6)))))) (.split 80 (.pack [8,22]) (.zero 23)))))) (.split 25 (.split 28 (.pack [20,5]) (.split 40 (.split 37 .done (.split 51 (.pack [18]) (.split 53 (.pack [6]) (.split 79 (.pack [22]) (.zero 7))))) (.split 67 (.split 8 (.pack [8]) (.split 23 (.pack [9]) (.split 50 (.pack [3]) (.split 66 (.pack [25]) (.zero 17))))) (.split 84 (.split 29 (.pack [21]) (.split 41 (.pack [10]) (.split 49 (.pack [3]) (.split 52 (.pack [8]) (.split 53 (.pack [7]) (.split 66 (.pack [17]) (.split 70 (.pack [18]) (.split 71 (.pack [18]) (.split 85 (.pack [25]) (.zero 16)))))))))) (.split 86 (.pack [25,1]) (.zero 26)))))) (.split 29 (.pack [21,27,5]) (.split 41 (.split 44 (.pack [27,8]) (.split 54 (.pack [19,8]) (.split 55 (.pack [20,8]) (.split 83 (.pack [8,24]) (.zero 10))))) (.split 49 (.split 3 (.pack [12,4]) (.split 33 (.pack [0,22]) (.split 36 (.pack [6,24]) (.split 50 (.split 8 (.pack [8]) (.split 23 (.pack [2]) (.split 66 (.pack [25]) (.split 67 (.pack [26]) (.zero 17))))) (.split 75 (.split 1 (.pack [13]) (.split 2 (.pack [14]) (.split 16 (.pack [20]) (.split 19 (.pack [15]) (.split 28 (.pack [20]) (.split 44 (.pack [10]) (.split 59 (.pack [1]) (.split 70 (.pack [18]) (.split 77 .done (.split 85 (.pack [16]) (.split 86 (.pack [26]) (.split 87 (.pack [27]) (.split 89 (.pack [14]) (.zero 11)))))))))))))) (.zero 3)))))) (.split 52 (.split 8 (.pack [17,6]) (.split 38 (.split 6 (.pack [9]) (.split 36 (.pack [3]) (.split 39 (.pack [25]) (.split 53 (.pack [7]) (.split 78 (.pack [23]) (.zero 6)))))) (.split 51 (.pack [7,18]) (.split 80 (.pack [23,22]) (.zero 8))))) (.split 53 (.split 6 (.pack [7,9]) (.split 36 (.pack [3,7]) (.split 39 (.pack [7,25]) (.split 78 (.pack [7,23]) (.zero 6))))) (.split 66 (.split 8 (.pack [8,25]) (.split 23 (.pack [25,2]) (.split 50 (.pack [3,25]) (.split 67 (.split 28 (.pack [20]) (.split 40 (.pack [7]) (.split 84 (.pack [16]) (.split 86 (.pack [11]) (.zero 26))))) (.zero 17))))) (.split 70 (.split 9 (.split 1 (.pack [13]) (.split 2 (.pack [14]) (.split 16 (.pack [20]) (.split 19 (.pack [15]) (.split 28 (.pack [20]) (.split 44 (.pack [10]) (.split 59 (.pack [1]) (.split 75 (.pack [3]) (.split 77 .done (.split 85 (.pack [16]) (.split 86 (.pack [25]) (.split 87 (.pack [27]) (.split 89 (.pack [14]) (.zero 11)))))))))))))) (.split 12 (.pack [19,11]) (.split 24 (.pack [25,24]) (.split 51 (.pack [7,8]) (.split 71 (.pack [16,27]) (.zero 18)))))) (.split 71 (.split 9 (.pack [27,5]) (.split 12 (.pack [27,19]) (.split 24 (.pack [25,27]) (.split 51 (.pack [7,8]) (.zero 18))))) (.split 84 (.split 28 (.pack [20,5]) (.split 40 (.split 37 .done (.split 51 (.pack [18]) (.split 79 (.pack [22]) (.zero 7)))) (.split 67 (.split 8 (.pack [8]) (.split 23 (.pack [9]) (.split 50 (.pack [3]) (.zero 17)))) (.split 86 (.pack [25,1]) (.zero 26))))) (.split 85 (.split 24 (.pack [18,24]) (.split 27 (.pack [19,9]) (.split 39 (.pack [6,9]) (.split 86 (.pack [26,1]) (.zero 25))))) (.zero 16)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 464 is kernel-checked. -/
theorem checked464 : checkParitySearch 8 (fun q => lane 256 q rows464) 0x10010 (allowed464.contains) tree464 0x3fdefcef9fed3f77beffbff 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 464 satisfy the full bottom equations. -/
theorem initial464 : checkSearchInitial 8 90 28 rows464 lambdas464 0x10010 0x2103106012c0884100400 0xc4180486c4c620c0243626 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 464. -/
theorem rhs464 : reconX bottomRColumns 0x2103106012c0884100400 = 0xc4180486c4c620c0243626 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 464 has a listed outside support. -/
theorem complete464 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x2103106012c0884100400)
    (hoff : bitCount 90 (outsideMask word 0x2103106012c0884100400) ≤ 3) :
    outsideMask word 0x2103106012c0884100400 ∈ allowed464 := by
  exact outside_mem_of_search 8 90 28 rows464 lambdas464 0x10010 0x2103106012c0884100400 0xc4180486c4c620c0243626 3
    bottomEColumns bottomETransposeColumns tree464 allowed464 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial464 checked464
    hw (he.trans rhs464) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 80 matches a certified search. -/
theorem matches20000 : records20000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 80. -/
theorem chunk_complete20000 (r : Fiber) (hr : r ∈ records20000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches20000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 81 matches a certified search. -/
theorem matches20250 : records20250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → (r.beta = 0x21022a120811442020008 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed463) ∨ (r.beta = 0x2103106012c0884100400 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed464))) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 81. -/
theorem chunk_complete20250 (r : Fiber) (hr : r ∈ records20250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches20250) r hr)) hweight
  rcases h with h0 | h1
  · exact search_census_transfer r 0x21022a120811442020008 3 allowed463 complete463 h0 word hw he hoff
  · exact search_census_transfer r 0x2103106012c0884100400 3 allowed464 complete464 h1 word hw he hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 82 matches a certified search. -/
theorem matches20500 : records20500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 82. -/
theorem chunk_complete20500 (r : Fiber) (hr : r ∈ records20500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches20500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 83 matches a certified search. -/
theorem matches20750 : records20750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 83. -/
theorem chunk_complete20750 (r : Fiber) (hr : r ∈ records20750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches20750) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 84 matches a certified search. -/
theorem matches21000 : records21000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 84. -/
theorem chunk_complete21000 (r : Fiber) (hr : r ∈ records21000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches21000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 85 matches a certified search. -/
theorem matches21250 : records21250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 85. -/
theorem chunk_complete21250 (r : Fiber) (hr : r ∈ records21250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches21250) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 86 matches a certified search. -/
theorem matches21500 : records21500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 86. -/
theorem chunk_complete21500 (r : Fiber) (hr : r ∈ records21500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches21500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 87 matches a certified search. -/
theorem matches21750 : records21750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 87. -/
theorem chunk_complete21750 (r : Fiber) (hr : r ∈ records21750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches21750) r hr)) hweight
  exact False.elim h

#print axioms chunk_complete20000
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch

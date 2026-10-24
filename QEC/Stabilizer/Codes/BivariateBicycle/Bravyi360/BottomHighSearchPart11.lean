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
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart11

noncomputable section
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch
open F2Mask PackedDigits FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 465. -/
noncomputable def rows465 : Nat := (Nat.lor 0x8000006000000000008009000000000000000000000000000000000000000003403040042014000c048804000000000000000000000000000000000000000001ad98c36c10046c1c1584020000000000000000000000000000000000000000001000000c0004000000100100000000000000000000000000000000000000000008000000c012000000080000000000000000000000000000000000000000000289ab836470016c301328000000000000000000000000000000000000000000000803c100b004a024422e00000000000000000000000000000000000000000000010000001802400000010000000000000000000000000000000000000000000000800000280120000000800000000000000000000000000000000000000000005c8013403101f8147002000000000000000000000000000000000000000000000020000003004800000020000000000000000000000000000000000000000000001000000500240000001000000000000000000000000000000000000000000000080000060012000000080000000000000000000000000000000000000000005d8412e00101651434029c0000000000000000000000000000000000000000005daa10640181681435020a0000000000000000000000000000000000000000030d8181e010846e0c102491 (Nat.shiftLeft 0x18000800000100120000000000000000000000000000000000000000000000000300010000002002400000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c0000800000100120000000000000000000000000000000000000000000000001800010000002002400000000000000000000000000000000000000000000000018000800000100120000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c000080000010012000000000000000000000000000000000000000000005c000700040160144009000000000000000000000000000000000000000000000000140002000000400480000000000000000000000000000000000000000000000001800080000010012000000000000000000000000000000000000000000200000030000000000200240000000000000000000000000000000000000000010000005000000000010012 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 465. -/
noncomputable def lambdas465 : Nat := (Nat.lor 0x800000000000000000000000000000000000000000000080088000000000000040000000000000000000000000000000000000000000018d98400000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000010d94c000000000000004000000000000000000000000000000000000000000000404c00000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000002d000400000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000002d800580000000000000040000000000000000000000000000000000000000002d900480000000000000020000000000000000000000000000000000000000008d80410000000000000001 (Nat.shiftLeft 0x100000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000002c000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 465. -/
noncomputable def allowed465 : List Nat := [0x10002000,0x1000000000010000000,0x20400040000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 465. -/
noncomputable def tree465 : ParitySearchTree := (.split 8 (.split 5 (.pack [5,17]) (.split 20 (.pack [24,8]) (.split 47 (.split 38 (.pack [5]) (.split 41 (.pack [11]) (.split 51 (.pack [21]) (.split 52 (.pack [0]) (.split 80 (.pack [25]) (.zero 8)))))) (.split 63 (.pack [8,26]) (.split 64 (.split 38 (.pack [5]) (.split 41 (.pack [11]) (.split 51 (.pack [21]) (.split 52 (.pack [20]) (.split 80 (.pack [25]) (.zero 8)))))) (.zero 18)))))) (.split 11 (.split 41 (.pack [8,28]) (.split 44 (.pack [29,6]) (.split 54 (.pack [22,6]) (.split 55 (.pack [23,14]) (.split 83 (.pack [26,14]) (.zero 11)))))) (.split 22 (.split 7 (.split 37 (.pack [4]) (.split 40 (.pack [20]) (.split 51 (.pack [8]) (.split 53 (.pack [14]) (.split 79 (.pack [25]) (.zero 7)))))) (.split 10 (.split 9 (.pack [21]) (.split 13 (.pack [23]) (.split 17 (.pack [24]) (.split 26 (.pack [28]) (.split 29 (.pack [28]) (.split 37 (.pack [7]) (.split 39 (.pack [27]) (.split 42 (.pack [12]) (.split 52 (.pack [8]) (.split 53 (.pack [7]) (.split 55 (.pack [23]) (.split 64 (.pack [18]) (.split 70 (.pack [21]) (.split 71 (.pack [21]) (.split 72 (.pack [23]) (.split 73 (.pack [22]) (.split 83 (.pack [11]) (.zero 9)))))))))))))))))) (.split 49 (.pack [3,5]) (.split 66 (.split 24 (.pack [21]) (.split 27 (.pack [22]) (.split 39 (.pack [20]) (.split 85 (.pack [28]) (.split 86 (.pack [14]) (.zero 27)))))) (.split 68 (.split 26 (.pack [20]) (.split 29 (.pack [29]) (.split 41 (.pack [8]) (.split 84 (.pack [12]) (.split 85 (.pack [27]) (.zero 28)))))) (.zero 19)))))) (.split 26 (.split 29 (.split 32 (.pack [24]) (.split 44 (.pack [11]) (.split 71 (.pack [21]) (.split 87 (.pack [15]) (.split 88 (.pack [16]) (.zero 29)))))) (.split 41 (.pack [8,11]) (.split 68 (.pack [19,14]) (.split 84 (.pack [12,20]) (.split 85 (.split 24 (.pack [21]) (.split 27 (.pack [22]) (.split 39 (.pack [14]) (.split 66 (.pack [19]) (.split 86 (.pack [20]) (.zero 27)))))) (.zero 28)))))) (.split 28 (.split 13 (.split 0 (.pack [12]) (.split 1 (.pack [16]) (.split 2 (.pack [17]) (.split 3 (.pack [15]) (.split 4 (.pack [16]) (.split 5 (.pack [18]) (.split 7 (.pack [19]) (.split 9 (.pack [21]) (.split 10 (.pack [19]) (.split 12 (.pack [21]) (.split 15 (.pack [15]) (.split 16 (.pack [23]) (.split 17 (.pack [17]) (.split 18 (.pack [25]) (.split 20 (.pack [18]) (.split 21 (.pack [25]) (.split 24 (.pack [21]) (.split 27 (.pack [22]) (.split 29 (.pack [28]) (.split 32 (.pack [24]) (.split 33 (.pack [25]) (.split 34 (.pack [4]) (.split 35 (.pack [5]) (.split 36 (.pack [3]) (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 39 (.pack [27]) (.split 40 (.pack [7]) (.split 41 (.pack [8]) (.split 42 (.pack [12]) (.split 44 (.pack [11]) (.split 47 (.pack [18]) (.split 48 (.pack [4]) (.split 49 (.pack [5]) (.split 50 (.pack [3]) (.split 51 (.pack [21]) (.split 52 (.pack [8]) (.split 53 (.pack [7]) (.split 54 (.pack [22]) (.split 55 (.pack [11]) (.split 58 (.pack [12]) (.split 59 (.pack [12]) (.split 60 (.pack [25]) (.split 61 (.pack [17]) (.split 62 (.pack [15]) (.split 63 (.pack [18]) (.split 64 (.zero 18) (.split 65 (.pack [20]) (.split 66 (.pack [19]) (.split 68 (.zero 19) (.split 70 (.pack [21]) (.split 71 (.zero 21) (.split 72 (.pack [23]) (.split 73 (.pack [22]) (.split 74 (.zero 22) (.split 75 (.zero 3) (.split 76 (.zero 4) (.split 77 (.zero 5) (.split 79 (.zero 7) (.split 80 (.zero 8) (.split 82 (.pack [26]) (.split 83 (.zero 9) (.split 84 (.zero 12) (.split 85 (.zero 28) (.split 86 (.zero 1) (.split 87 (.zero 15) (.split 88 (.zero 13) (.split 89 (.zero 0) .done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.split 16 (.pack [16,9]) (.split 55 (.split 41 (.pack [8]) (.split 44 (.pack [29]) (.split 54 (.pack [22]) (.split 83 (.pack [26]) (.zero 11))))) (.split 72 (.split 0 (.pack [12]) (.split 1 (.pack [16]) (.split 2 (.pack [17]) (.split 3 (.pack [15]) (.split 4 (.pack [16]) (.split 5 (.pack [18]) (.split 7 (.pack [19]) (.split 9 (.pack [21]) (.split 10 (.pack [19]) (.split 12 (.pack [21]) (.split 15 (.pack [15]) (.split 17 (.pack [17]) (.split 18 (.pack [25]) (.split 20 (.pack [18]) (.split 21 (.pack [25]) (.split 24 (.pack [21]) (.split 27 (.pack [22]) (.split 29 (.pack [28]) (.split 32 (.pack [24]) (.split 33 (.pack [25]) (.split 34 (.pack [4]) (.split 35 (.pack [5]) (.split 36 (.pack [3]) (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 39 (.pack [27]) (.split 40 (.pack [7]) (.split 41 (.pack [8]) (.split 42 (.pack [12]) (.split 44 (.pack [11]) (.split 47 (.pack [18]) (.split 48 (.pack [4]) (.split 49 (.pack [5]) (.split 50 (.pack [3]) (.split 51 (.pack [21]) (.split 52 (.pack [8]) (.split 53 (.pack [7]) (.split 54 (.pack [11]) (.split 58 (.pack [12]) (.split 59 (.pack [12]) (.split 60 (.pack [25]) (.split 61 (.pack [17]) (.split 62 (.pack [15]) (.split 63 (.pack [18]) (.split 64 (.zero 18) (.split 65 (.pack [20]) (.split 66 (.pack [19]) (.split 68 (.zero 19) (.split 70 (.pack [21]) (.split 71 (.zero 21) (.split 73 (.pack [22]) (.split 74 (.zero 22) (.split 75 (.zero 3) (.split 76 (.zero 4) (.split 77 (.zero 5) (.split 79 (.zero 7) (.split 80 (.zero 8) (.split 82 (.pack [26]) (.split 83 (.zero 9) (.split 84 (.zero 12) (.split 85 (.zero 28) (.split 86 (.zero 1) (.split 87 (.zero 15) (.split 88 (.zero 13) (.split 89 (.zero 0) .done))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.split 74 (.pack [22,2]) (.zero 23)))))) (.split 37 (.split 4 (.pack [7,16]) (.split 34 (.split 7 (.pack [19]) (.split 40 (.pack [20]) (.split 51 (.pack [8]) (.split 53 (.pack [14]) (.split 79 (.pack [25]) (.zero 7)))))) (.split 48 (.pack [5,7]) (.split 50 (.pack [3,7]) (.split 76 (.pack [24,7]) (.zero 4)))))) (.split 38 (.split 41 (.pack [11,28]) (.split 51 (.pack [7,21]) (.split 52 (.split 5 (.pack [18]) (.split 35 (.pack [1]) (.split 48 (.pack [4]) (.split 49 (.pack [19]) (.split 77 (.pack [14]) (.zero 5)))))) (.split 80 (.pack [5,25]) (.zero 8))))) (.split 40 (.split 7 (.pack [19,10]) (.split 51 (.pack [8,21]) (.split 53 (.split 2 (.pack [17]) (.split 15 (.pack [22]) (.split 18 (.pack [25]) (.split 27 (.pack [22]) (.split 42 (.pack [12]) (.split 44 (.pack [11]) (.split 58 (.pack [12]) (.split 70 (.pack [21]) (.split 76 (.pack [4]) (.split 77 (.pack [5]) (.split 86 (.pack [27]) (.split 88 (.pack [29]) (.split 89 (.pack [17]) (.zero 14)))))))))))))) (.split 79 (.pack [25,9]) (.zero 7))))) (.split 50 (.pack [4,3,9]) (.split 64 (.split 5 (.pack [5,17]) (.split 20 (.pack [24,6]) (.split 47 (.split 2 (.pack [17]) (.split 3 (.pack [3]) (.split 4 (.pack [4]) (.split 7 (.pack [7]) (.split 9 (.pack [21]) (.split 18 (.pack [25]) (.split 21 (.pack [25]) (.split 32 (.pack [24]) (.split 34 (.pack [4]) (.split 48 (.pack [4]) (.split 61 (.pack [17]) (.split 62 (.pack [15]) (.split 63 (.zero 18) (.split 65 (.pack [20]) (.split 68 (.pack [19]) (.split 74 (.pack [23]) (.split 79 (.pack [7]) (.split 80 (.pack [25]) (.split 82 (.pack [26]) (.split 83 (.pack [26]) (.split 84 (.pack [20]) (.split 86 (.pack [20]) (.zero 2))))))))))))))))))))))) (.split 63 (.split 21 (.pack [25]) (.split 24 (.pack [21]) (.split 36 (.pack [3]) (.split 82 (.pack [20]) (.split 83 (.pack [11]) (.zero 26)))))) (.zero 18))))) (.split 65 (.split 9 (.pack [21,6]) (.split 10 (.pack [19,10]) (.split 13 (.split 16 (.pack [16]) (.split 55 (.pack [11]) (.split 72 (.pack [9]) (.split 74 (.pack [22]) (.zero 23))))) (.split 17 (.pack [24,17]) (.split 29 (.pack [28,29]) (.split 39 (.pack [27,10]) (.split 42 (.split 0 (.pack [15]) (.split 12 (.pack [21]) (.split 58 .done (.split 59 (.pack [24]) (.split 84 (.pack [28]) (.zero 12)))))) (.split 52 (.pack [8,6]) (.split 53 (.pack [7,14]) (.split 55 (.pack [23,11]) (.split 70 (.pack [21,14]) (.split 71 (.pack [21,29]) (.split 72 (.split 16 (.pack [16]) (.split 74 (.pack [22]) (.zero 23))) (.split 73 (.split 12 (.pack [21]) (.split 15 (.pack [15]) (.split 27 (.pack [27]) (.split 54 (.pack [11]) (.split 74 (.pack [23]) (.zero 22)))))) (.split 83 (.pack [11,20]) (.zero 9)))))))))))))))) (.split 66 (.split 7 (.pack [7,27]) (.split 10 (.split 24 (.pack [21]) (.split 27 (.pack [22]) (.split 39 (.pack [9]) (.split 85 (.pack [28]) (.split 86 (.pack [20]) (.zero 27)))))) (.split 49 (.pack [3,5]) (.split 68 (.pack [28,0]) (.zero 19))))) (.split 82 (.split 21 (.pack [25,9]) (.split 24 (.pack [27,21]) (.split 36 (.pack [3,6]) (.split 63 (.pack [18,9]) (.split 83 (.pack [20,11]) (.zero 26)))))) (.split 83 (.split 41 (.pack [8,26]) (.split 44 (.pack [26,29]) (.split 54 (.pack [26,22]) (.split 55 (.pack [26,23]) (.zero 11))))) (.split 84 (.split 29 (.pack [12,29]) (.split 41 (.pack [11,8]) (.split 68 (.pack [19,12]) (.split 85 (.pack [27,12]) (.zero 28))))) (.split 86 (.split 24 (.pack [26,21]) (.split 27 (.split 12 (.pack [12]) (.split 15 (.pack [15]) (.split 54 (.pack [11]) (.split 73 (.pack [1]) (.split 74 (.pack [23]) (.zero 22)))))) (.split 39 (.split 9 (.pack [21]) (.split 20 (.pack [18]) (.split 21 (.pack [26]) (.split 35 (.pack [5]) (.split 36 (.pack [26]) (.split 48 (.pack [4]) (.split 52 (.pack [8]) (.split 53 (.pack [7]) (.split 62 (.pack [15]) (.split 68 (.pack [19]) (.split 79 (.pack [7]) (.zero 6)))))))))))) (.split 85 (.pack [28,14]) (.zero 27))))) (.zero 20)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 465 is kernel-checked. -/
theorem checked465 : checkParitySearch 8 (fun q => lane 256 q rows465) 0x102247 (allowed465.contains) tree465 0x3fdbfd7fcff97ff3d77bfbf 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 465 satisfy the full bottom equations. -/
theorem initial465 : checkSearchInitial 8 90 30 rows465 lambdas465 0x102247 0x2402803006800c2884040 0xa00c0184806500600c2403 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 465. -/
theorem rhs465 : reconX bottomRColumns 0x2402803006800c2884040 = 0xa00c0184806500600c2403 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 465 has a listed outside support. -/
theorem complete465 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x2402803006800c2884040)
    (hoff : bitCount 90 (outsideMask word 0x2402803006800c2884040) ≤ 3) :
    outsideMask word 0x2402803006800c2884040 ∈ allowed465 := by
  exact outside_mem_of_search 8 90 30 rows465 lambdas465 0x102247 0x2402803006800c2884040 0xa00c0184806500600c2403 3
    bottomEColumns bottomETransposeColumns tree465 allowed465 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial465 checked465
    hw (he.trans rhs465) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 466. -/
noncomputable def rows466 : Nat := (Nat.lor 0x1800010000002002400000000000000000000000000000000000000000000c000e800480600650082000000000000000000000000000000000000000000000000280004000000800900000000000000000000000000000000000000000010000005000000000010012000000000000000000000000000000000000000002d000005a0014000002d02800000000000000000000000000000000000000000008000000c01200000008000000000000000000000000000000000000000000002406000ac0010030034402000000000000000000000000000000000000000000e5ae42580014cc245002220000000000000000000000000000000000000000000080000028012000000080000000000000000000000000000000000000000000e128e018201094124344620000000000000000000000000000000000000000000020000003004800000020000000000000000000000000000000000000000000001000000500240000001000000000000000000000000000000000000000000000080000060012000000080000000000000000000000000000000000000000020d840050004065061e00680000000000000000000000000000000000000000024daa00520090680617406a000000000000000000000000000000000000000000602c405880d002400ac02a (Nat.shiftLeft 0x1800080000010012000000000000000000000000000000000000000000000000300002000000400480000000000000000000000000000000000000000000000003000100000020024000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c00008000001001200000000000000000000000000000000000000000000000018000100000020024000000000000000000000000000000000000000000000000180008000001001200000000000000000000000000000000000000000000000030000200000040048000000000000000000000000000000000000000000000000600004000000800900000000000000000000000000000000000000000000000006000200000040048000000000000000000000000000000000000000000000000c000080000010012000000000000000000000000000000000000000000000000140002000000400480 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 466. -/
noncomputable def lambdas466 : Nat := (Nat.lor 0x2000000000000000000000000000000000000000000000000c00100000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000005800000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000060004000000000004000000000000000000000000000000000000000000010996004c0000000000020000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000010090404c000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000d8000c0000000000000040000000000000000000000000000000000000000000d9000c8000000000000020000000000000000000000000000000000000000010012005c00000000000001 (Nat.shiftLeft 0x100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 466. -/
noncomputable def allowed466 : List Nat := [0x12000000,0x80000000010000040,0x20000200000000000020,0x400028000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 466. -/
noncomputable def tree466 : ParitySearchTree := (.split 5 (.split 35 (.split 3 (.pack [3]) (.split 12 (.pack [17]) (.split 14 (.pack [18]) (.split 15 (.pack [19]) (.split 17 (.pack [21]) (.split 42 (.pack [27]) (.split 44 (.pack [10]) (.split 57 (.pack [20]) (.split 59 (.pack [21]) (.split 60 (.pack [22]) (.split 62 (.pack [12]) (.split 84 (.pack [26]) (.split 86 (.pack [25]) (.split 87 (.pack [28]) (.split 89 (.pack [27]) (.zero 11)))))))))))))))) (.split 38 (.pack [14,11]) (.split 48 (.pack [15,4]) (.split 49 (.pack [16,3]) (.split 77 (.split 15 (.pack [19]) (.split 18 (.pack [22]) (.split 30 (.pack [27]) (.split 57 .done (.split 76 (.pack [4]) (.zero 20)))))) (.zero 5)))))) (.split 11 (.split 14 (.split 41 (.pack [26]) (.split 44 (.pack [28]) (.split 54 (.pack [19]) (.split 55 (.pack [9]) (.split 83 (.pack [23]) (.zero 10)))))) (.split 26 (.split 41 (.pack [14]) (.split 44 (.pack [26]) (.split 54 (.pack [26]) (.split 55 (.pack [26]) (.split 83 (.pack [26]) (.zero 10)))))) (.split 53 (.pack [7,10]) (.split 69 (.pack [10,27]) (.split 70 (.pack [17,10]) (.zero 18)))))) (.split 20 (.split 17 (.split 3 (.pack [3]) (.split 12 (.pack [17]) (.split 14 (.pack [18]) (.split 15 (.pack [19]) (.split 42 (.pack [27]) (.split 44 (.pack [10]) (.split 57 (.pack [20]) (.split 59 (.pack [21]) (.split 60 (.pack [22]) (.split 62 (.pack [12]) (.split 84 (.pack [26]) (.split 86 (.pack [25]) (.split 87 (.pack [28]) (.split 89 (.pack [27]) (.zero 11))))))))))))))) (.split 32 (.pack [28,2]) (.split 59 (.split 3 (.pack [3]) (.split 12 (.pack [17]) (.split 14 (.pack [18]) (.split 15 (.pack [19]) (.split 42 (.pack [27]) (.split 44 (.pack [10]) (.split 57 (.pack [20]) (.split 60 (.pack [22]) (.split 62 (.pack [12]) (.split 84 (.pack [26]) (.split 86 (.pack [25]) (.split 87 (.pack [28]) (.split 89 (.pack [27]) (.zero 11)))))))))))))) (.split 75 (.pack [3,9]) (.split 76 (.pack [4,20]) (.zero 21)))))) (.split 22 (.split 7 (.pack [13,7]) (.split 10 (.split 3 (.pack [3]) (.split 6 (.pack [15]) (.split 17 (.pack [21]) (.split 18 (.pack [20]) (.split 19 (.pack [13]) (.split 25 (.pack [25]) (.split 26 (.pack [18]) (.split 32 (.pack [21]) (.split 34 (.pack [4]) (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 46 (.pack [13]) (.split 60 (.pack [22]) (.split 62 (.pack [12]) (.split 74 (.pack [19]) (.split 79 (.pack [7]) (.split 80 (.pack [22]) (.split 82 (.pack [23]) (.split 83 (.pack [10]) (.split 89 (.pack [27]) (.zero 2))))))))))))))))))))) (.split 49 (.pack [5,3]) (.split 66 (.pack [24,14]) (.split 68 (.pack [15,26]) (.zero 16)))))) (.split 25 (.split 28 (.split 1 (.pack [12]) (.split 3 (.pack [3]) (.split 4 (.pack [12]) (.split 6 (.pack [15]) (.split 7 (.pack [13]) (.split 9 (.pack [15]) (.split 10 (.pack [16]) (.split 12 (.pack [17]) (.split 14 (.pack [18]) (.split 15 (.pack [19]) (.split 16 (.pack [12]) (.split 17 (.pack [21]) (.split 18 (.pack [20]) (.split 19 (.pack [13]) (.split 21 (.pack [15]) (.split 24 (.pack [17]) (.split 26 (.pack [18]) (.split 27 (.pack [19]) (.split 29 (.pack [26]) (.split 30 (.pack [20]) (.split 32 (.pack [21]) (.split 33 (.pack [22]) (.split 34 (.pack [4]) (.split 35 (.pack [5]) (.split 36 (.pack [3]) (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 39 (.pack [24]) (.split 40 (.pack [7]) (.split 41 (.pack [26]) (.split 42 (.pack [27]) (.split 44 (.pack [10]) (.split 46 (.pack [13]) (.split 47 (.pack [14]) (.split 48 (.pack [15]) (.split 49 (.pack [5]) (.split 50 (.pack [3]) (.split 51 (.pack [17]) (.split 53 (.pack [7]) (.split 54 (.pack [19]) (.split 55 (.pack [10]) (.split 57 (.pack [20]) (.split 59 (.pack [21]) (.split 60 (.pack [22]) (.split 62 (.pack [12]) (.split 63 (.pack [13]) (.split 65 (.zero 13) (.split 66 (.pack [16]) (.split 67 (.pack [15]) (.split 68 (.zero 15) (.split 69 (.pack [18]) (.split 70 (.zero 18) (.split 71 (.zero 17) (.split 73 (.pack [19]) (.split 74 (.zero 19) (.split 75 (.zero 3) (.split 76 (.zero 4) (.split 77 (.zero 5) (.split 79 (.zero 7) (.split 80 (.zero 22) (.split 82 (.pack [14]) (.split 83 (.zero 10) (.split 84 (.pack [26]) (.split 85 (.zero 9) (.split 86 (.zero 0) (.split 87 (.zero 6) (.split 88 (.zero 12) (.split 89 (.zero 1) .done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.split 40 (.split 7 (.pack [16]) (.split 37 (.pack [4]) (.split 51 (.pack [17]) (.split 53 (.pack [18]) (.split 79 (.pack [22]) (.zero 7)))))) (.split 67 (.pack [15,14]) (.split 84 (.pack [26,11]) (.split 86 (.pack [24,11]) (.zero 25)))))) (.split 26 (.split 14 (.pack [26,1]) (.split 53 (.pack [7,26]) (.split 69 (.pack [26,27]) (.split 70 (.pack [17,26]) (.zero 18))))) (.split 37 (.split 4 (.pack [13,12]) (.split 34 (.split 7 (.pack [13]) (.split 40 (.pack [25]) (.split 51 (.pack [17]) (.split 53 (.pack [18]) (.split 79 (.pack [22]) (.zero 7)))))) (.split 48 (.pack [5,15]) (.split 50 (.pack [3,7]) (.split 76 (.pack [21,20]) (.zero 4)))))) (.split 38 (.split 35 (.split 1 (.pack [12]) (.split 10 (.pack [16]) (.split 14 (.pack [18]) (.split 16 (.pack [12]) (.split 17 (.pack [21]) (.split 28 (.pack [25]) (.split 29 (.pack [26]) (.split 40 (.pack [25]) (.split 54 (.pack [10]) (.split 55 (.pack [10]) (.split 57 (.pack [20]) (.split 59 (.pack [21]) (.split 73 (.pack [19]) (.split 74 (.pack [19]) (.split 82 (.pack [23]) (.split 85 (.pack [26]) (.zero 9))))))))))))))))) (.split 48 (.pack [4,15]) (.split 49 (.pack [16,3]) (.split 77 (.pack [20,6]) (.zero 5))))) (.split 47 (.split 1 (.split 4 (.pack [4]) (.split 16 (.pack [9]) (.split 60 (.pack [22]) (.split 62 (.pack [11]) (.split 88 (.pack [28]) (.zero 12)))))) (.split 10 (.pack [16,2]) (.split 14 (.pack [18,11]) (.split 16 (.split 4 (.pack [4]) (.split 60 (.pack [22]) (.split 62 (.pack [11]) (.split 88 (.pack [28]) (.zero 12))))) (.split 17 (.split 32 (.pack [28]) (.split 59 (.pack [9]) (.split 75 (.pack [3]) (.split 76 (.pack [4]) (.zero 21))))) (.split 28 (.pack [25,2]) (.split 29 (.pack [26,28]) (.split 40 (.pack [25,7]) (.split 54 (.pack [10,19]) (.split 55 (.split 41 (.pack [26]) (.split 44 (.pack [28]) (.split 83 (.pack [23]) (.zero 10)))) (.split 57 (.split 15 (.pack [19]) (.split 18 (.pack [22]) (.split 30 (.pack [27]) (.split 76 (.pack [21]) (.split 77 (.pack [5]) (.zero 20)))))) (.split 59 (.pack [21,11]) (.split 73 (.pack [19,1]) (.split 74 (.pack [19,8]) (.split 82 (.pack [23,0]) (.split 85 (.pack [26,24]) (.zero 9))))))))))))))))) (.split 50 (.pack [4,3,9]) (.split 63 (.split 4 (.pack [4,23]) (.split 7 (.pack [16,7]) (.split 19 (.pack [23,0]) (.split 46 (.pack [23,0]) (.split 65 (.split 66 (.pack [16]) (.split 67 (.pack [25]) (.split 82 .done (.split 83 (.pack [10]) (.zero 14))))) (.zero 13)))))) (.split 65 (.split 4 (.pack [4,12]) (.split 7 (.pack [16,7]) (.split 19 (.split 1 (.pack [12]) (.split 10 (.pack [16]) (.split 14 (.pack [18]) (.split 16 (.pack [12]) (.split 17 (.pack [21]) (.split 28 (.pack [25]) (.split 29 (.pack [26]) (.split 40 (.pack [7]) (.split 54 (.pack [10]) (.split 55 (.pack [10]) (.split 57 (.pack [20]) (.split 59 (.pack [21]) (.split 73 (.pack [19]) (.split 74 (.pack [19]) (.split 82 (.pack [14]) (.split 85 (.pack [26]) (.zero 9))))))))))))))))) (.split 46 (.split 1 (.pack [12]) (.split 10 (.pack [16]) (.split 14 (.pack [18]) (.split 16 (.pack [12]) (.split 17 (.pack [21]) (.split 28 (.pack [25]) (.split 29 (.pack [26]) (.split 40 (.pack [7]) (.split 54 (.pack [10]) (.split 55 (.pack [10]) (.split 57 (.pack [20]) (.split 59 (.pack [21]) (.split 73 (.pack [19]) (.split 74 (.pack [19]) (.split 82 (.pack [14]) (.split 85 (.pack [26]) (.zero 9))))))))))))))))) (.zero 13))))) (.split 66 (.pack [16,24,2]) (.split 67 (.split 28 (.split 6 .done (.split 9 (.pack [17]) (.split 21 (.pack [23]) (.split 48 (.pack [4]) (.split 68 (.pack [16]) (.zero 15)))))) (.split 40 (.pack [7,15]) (.split 84 (.pack [26,11]) (.split 86 (.pack [24,15]) (.zero 25))))) (.split 82 (.split 21 (.pack [15,22]) (.split 24 (.pack [24,17]) (.split 36 (.split 3 (.pack [2]) (.split 33 (.pack [22]) (.split 49 (.pack [16]) (.split 75 (.pack [21]) (.zero 3))))) (.split 83 (.zero 14) (.zero 23))))) (.split 83 (.split 21 (.pack [10,15]) (.split 24 (.pack [10,24]) (.split 36 (.pack [10,3]) (.zero 23)))) (.zero 14)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 466 is kernel-checked. -/
theorem checked466 : checkParitySearch 8 (fun q => lane 256 q rows466) 0x4206 (allowed466.contains) tree466 0x3fdbefedaefd7ff7f7fdefa 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 466 satisfy the full bottom equations. -/
theorem initial466 : checkSearchInitial 8 90 29 rows466 lambdas466 0x4206 0x241012510280080802105 0x4944084804024a2042402 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 466. -/
theorem rhs466 : reconX bottomRColumns 0x241012510280080802105 = 0x4944084804024a2042402 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 466 has a listed outside support. -/
theorem complete466 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x241012510280080802105)
    (hoff : bitCount 90 (outsideMask word 0x241012510280080802105) ≤ 3) :
    outsideMask word 0x241012510280080802105 ∈ allowed466 := by
  exact outside_mem_of_search 8 90 29 rows466 lambdas466 0x4206 0x241012510280080802105 0x4944084804024a2042402 3
    bottomEColumns bottomETransposeColumns tree466 allowed466 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial466 checked466
    hw (he.trans rhs466) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 467. -/
noncomputable def rows467 : Nat := (Nat.lor 0xc0000800000100120000000000000000000000000000000000000000000000001400020000004004800000000000000000000000000000000000000000008180000000000c00d880090000000000000000000000000000000000000000002000000a000800000020020000000000000000000000000000000000000000001000000c000400000010010000000000000000000000000000000000000000000806600160120034032000000000000000000000000000000000000000000000040000014009000000040000000000000000000000000000000000000000000008066c802484a036d322200000000000000000000000000000000000000000000d00028018822006d00020000000000000000000000000000000000000000000008000002801200000008000000000000000000000000000000000000000000241006e9614b09404de00080000000000000000000000000000000000000000000c20180002202806e4022800000000000000000000000000000000000000000000080000060012000000080000000000000000000000000000000000000000030184028000200500d300a20000000000000000000000000000000000000000000002000000a004800000020000000000000000000000000000000000000000034182028700900e60d100a3 (Nat.shiftLeft 0x18000800000100120000000000000000000000000000000000000000000000002800040000008009000000000000000000000000000000000000000000000000300002000000400480000000000000000000000000000000000000000000000003000100000020024000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c00008000001001200000000000000000000000000000000000000000000000018000100000020024000000000000000000000000000000000000000000000000180008000001001200000000000000000000000000000000000000000000000028000400000080090000000000000000000000000000000000000000000000003000020000004004800000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000a00010000002002400 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 467. -/
noncomputable def lambdas467 : Nat := (Nat.lor 0x100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000180000000000000008000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000006800000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000004069200000000000002000000000000000000000000000000000000000000000c000200000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000008092c8000000000000400000000000000000000000000000000000000000000c000480000000000000200000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000018001600000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000184016800000000000001 (Nat.shiftLeft 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000002000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 467. -/
noncomputable def allowed467 : List Nat := [0x20020002000000000,0x800008000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 467. -/
noncomputable def tree467 : ParitySearchTree := (.split 13 (.split 10 (.pack [14,9]) (.split 25 (.pack [12,24]) (.split 52 (.pack [12,7]) (.split 69 (.pack [12,26]) (.split 71 (.pack [15,12]) (.zero 16)))))) (.split 16 (.split 19 (.split 0 (.pack [11]) (.split 3 (.pack [3]) (.split 15 (.pack [17]) (.split 20 (.pack [20]) (.split 22 (.pack [14]) (.split 23 (.pack [7]) (.split 34 (.pack [1]) (.split 35 (.pack [0]) (.split 79 (.pack [6]) (.split 80 (.pack [21]) (.split 87 (.pack [28]) (.zero 13)))))))))))) (.split 31 (.pack [1,27]) (.split 58 (.pack [11,4]) (.split 75 (.pack [3,20]) (.split 77 (.pack [18,8]) (.zero 19)))))) (.split 17 (.split 20 (.split 0 (.pack [11]) (.split 3 (.pack [3]) (.split 15 (.pack [17]) (.split 19 (.pack [19]) (.split 22 (.pack [14]) (.split 23 (.pack [8]) (.split 34 (.pack [1]) (.split 35 (.pack [2]) (.split 79 (.pack [6]) (.split 80 (.pack [21]) (.split 87 (.pack [28]) (.zero 13)))))))))))) (.split 32 (.pack [28,4]) (.split 59 (.pack [12,11]) (.split 75 (.pack [19,3]) (.split 76 (.pack [18,8]) (.zero 20)))))) (.split 26 (.split 29 (.pack [28,7]) (.split 41 (.split 28 (.pack [24]) (.split 44 (.pack [28]) (.split 53 (.pack [6]) (.split 54 (.pack [17]) (.split 56 (.pack [9]) (.split 69 (.pack [16]) (.split 70 (.pack [27]) (.split 73 (.pack [17]) (.split 74 (.pack [17]) (.split 83 (.pack [22]) (.zero 10))))))))))) (.split 68 (.split 7 (.pack [6]) (.split 10 (.pack [16]) (.split 22 (.pack [13]) (.split 49 (.pack [3]) (.split 66 (.pack [23]) (.zero 14)))))) (.split 84 (.pack [11,24]) (.split 85 (.pack [12,23]) (.zero 25)))))) (.split 28 (.split 25 (.pack [16,27]) (.split 40 (.pack [6,9]) (.split 67 (.split 31 (.pack [19]) (.split 43 (.pack [9]) (.split 70 (.pack [15]) (.split 87 (.pack [28]) (.split 89 (.pack [26]) (.zero 27)))))) (.split 84 (.pack [25,11]) (.split 86 (.pack [23,27]) (.zero 24)))))) (.split 29 (.pack [25,28,8]) (.split 41 (.split 68 (.split 7 (.pack [6]) (.split 10 (.pack [16]) (.split 22 (.pack [13]) (.split 49 (.pack [3]) (.split 66 (.pack [23]) (.zero 14)))))) (.split 84 (.pack [24,11]) (.split 85 (.pack [12,23]) (.zero 25)))) (.split 44 (.split 32 (.pack [20,4]) (.split 71 (.pack [16,15]) (.split 87 (.pack [27,13]) (.split 88 (.pack [26,4]) (.zero 28))))) (.split 53 (.split 7 (.split 10 (.pack [16]) (.split 22 (.pack [13]) (.split 49 (.pack [3]) (.split 66 (.pack [23]) (.split 68 (.pack [25]) (.zero 14)))))) (.split 37 (.split 5 (.pack [4]) (.split 20 (.pack [20]) (.split 22 (.pack [14]) (.split 23 (.pack [13]) (.split 25 (.pack [16]) (.split 47 (.pack [1]) (.split 51 (.pack [6]) (.split 52 (.pack [16]) (.split 63 (.pack [22]) (.split 65 .done (.split 80 (.pack [21]) (.split 82 (.pack [22]) (.split 83 (.pack [22]) (.zero 7)))))))))))))) (.split 40 (.pack [24,9]) (.split 51 (.pack [15,7]) (.split 79 (.pack [21,8]) (.zero 6)))))) (.split 54 (.pack [17,9,5]) (.split 56 (.split 10 (.pack [16,14]) (.split 40 (.pack [6,24]) (.split 43 (.pack [12,27]) (.split 82 (.split 21 (.pack [21]) (.split 24 (.pack [15]) (.split 36 (.pack [3]) (.split 63 (.pack [8]) (.split 83 (.pack [10]) (.zero 22)))))) (.zero 9))))) (.split 69 (.split 10 (.pack [9,14]) (.split 25 (.pack [24,26]) (.split 52 (.pack [26,7]) (.split 71 (.pack [28,15]) (.zero 16))))) (.split 70 (.split 31 (.pack [19,15]) (.split 43 (.pack [9,12]) (.split 87 (.pack [28,13]) (.split 89 (.pack [26,15]) (.zero 27))))) (.split 73 (.split 12 (.pack [15,1]) (.split 15 (.pack [1,18]) (.split 27 (.pack [26,1]) (.split 74 (.pack [10,1]) (.zero 17))))) (.split 74 (.split 12 (.pack [15,11]) (.split 15 (.pack [18,13]) (.split 27 (.pack [26,23]) (.zero 17)))) (.split 83 (.split 21 (.pack [21,8]) (.split 24 (.pack [15,23]) (.split 36 (.pack [3,7]) (.split 63 (.split 0 (.pack [11]) (.split 1 (.pack [1]) (.split 3 (.pack [3]) (.split 5 (.pack [7]) (.split 7 (.pack [6]) (.split 9 (.pack [15]) (.split 10 (.pack [16]) (.split 12 (.pack [17]) (.split 15 (.pack [17]) (.split 18 (.pack [18]) (.split 19 (.pack [19]) (.split 20 (.pack [20]) (.split 22 (.pack [14]) (.split 23 (.pack [13]) (.split 25 (.pack [16]) (.split 27 (.zero 17) (.split 30 (.pack [18]) (.split 31 (.pack [1]) (.split 32 (.pack [20]) (.split 33 (.pack [3]) (.split 34 (.pack [1]) (.split 35 (.pack [13]) (.split 37 (.pack [6]) (.split 39 (.pack [23]) (.split 40 (.pack [6]) (.split 42 (.pack [26]) (.split 43 (.pack [9]) (.split 45 (.pack [1]) (.split 47 (.zero 1) (.split 49 (.pack [14]) (.split 50 (.pack [3]) (.split 51 (.pack [15]) (.split 52 (.pack [16]) (.split 57 (.pack [18]) (.split 58 (.pack [19]) (.split 59 (.pack [11]) (.split 60 (.pack [21]) (.split 65 (.pack [7]) (.split 66 (.pack [8]) (.split 67 (.zero 8) (.split 68 (.zero 14) (.split 71 (.zero 15) (.split 75 (.zero 3) (.split 76 (.zero 20) (.split 77 (.zero 18) (.split 79 (.zero 6) (.split 80 (.zero 21) (.split 82 (.zero 4) (.split 84 (.zero 11) (.split 85 (.zero 12) (.split 86 (.zero 23) (.split 87 (.zero 13) (.split 88 (.zero 28) (.split 89 (.zero 0) .done)))))))))))))))))))))))))))))))))))))))))))))))))))))) (.split 82 (.pack [9,8]) (.zero 22)))))) (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 467 is kernel-checked. -/
theorem checked467 : checkParitySearch 8 (fun q => lane 256 q rows467) 0x435 (allowed467.contains) tree467 0x3fdbefe9f7ebfbfffffb6ab 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 467 satisfy the full bottom equations. -/
theorem initial467 : checkSearchInitial 8 90 29 rows467 lambdas467 0x435 0x241016081404000004954 0x582050024002c10280120 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 467. -/
theorem rhs467 : reconX bottomRColumns 0x241016081404000004954 = 0x582050024002c10280120 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 467 has a listed outside support. -/
theorem complete467 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x241016081404000004954)
    (hoff : bitCount 90 (outsideMask word 0x241016081404000004954) ≤ 3) :
    outsideMask word 0x241016081404000004954 ∈ allowed467 := by
  exact outside_mem_of_search 8 90 29 rows467 lambdas467 0x435 0x241016081404000004954 0x582050024002c10280120 3
    bottomEColumns bottomETransposeColumns tree467 allowed467 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial467 checked467
    hw (he.trans rhs467) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 468. -/
noncomputable def rows468 : Nat := (Nat.lor 0x300002000000400480000000000000000000000000000000000000000008180000000000c00d880090000000000000000000000000000000000000000002000000a000800000020020000000000000000000000000000000000000000001000000c0004000000100100000000000000000000000000000000000000000008066001601200340320000000000000000000000000000000000000000000000400000140090000000400000000000000000000000000000000000000000000580665002405a024c323000000000000000000000000000000000000000000000d00a30008022004c0250000000000000000000000000000000000000000000000800000280120000000800000000000000000000000000000000000000000021100c41604119414ca25600000000000000000000000000000000000000000005c20130002012814e0026000000000000000000000000000000000000000000341907406201028047b036200000000000000000000000000000000000000000000080000060012000000080000000000000000000000000000000000000000030184028000200500d300a20000000000000000000000000000000000000000000002000000a004800000020000000000000000000000000000000000000000034182028700900e60d100a3 (Nat.shiftLeft 0x1800080000010012000000000000000000000000000000000000000000000000280004000000800900000000000000000000000000000000000000000000000030000200000040048000000000000000000000000000000000000000000000000300010000002002400000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c00008000001001200000000000000000000000000000000000000000000000018000100000020024000000000000000000000000000000000000000000000000180008000001001200000000000000000000000000000000000000000000000028000400000080090000000000000000000000000000000000000000000000003000020000004004800000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c0000800000100120000000000000000000000000000000000000000000000001400020000004004800000000000000000000000000000000000000000000000018000800000100120 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 468. -/
noncomputable def lambdas468 : Nat := (Nat.lor 0x400000000000000000000000000000000000000000000000180000000000000008000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000006800000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000024069000000000000002000000000000000000000000000000000000000000000c0040000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000002080d048000000000000400000000000000000000000000000000000000000002c0004000000000000002000000000000000000000000000000000000000000001809468000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000018001600000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000184016800000000000001 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000100000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 468. -/
noncomputable def allowed468 : List Nat := [0x800008000000000000100]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 468. -/
noncomputable def tree468 : ParitySearchTree := (.split 13 (.split 1 (.pack [1,8]) (.split 43 (.pack [10,28]) (.split 57 (.pack [20,8]) (.split 59 (.pack [22,12]) (.split 85 (.pack [26,25]) (.zero 13)))))) (.split 16 (.split 19 (.split 0 (.pack [12]) (.split 3 (.pack [15]) (.split 15 (.pack [19]) (.split 20 (.pack [16]) (.split 22 (.pack [17]) (.split 23 (.pack [8]) (.split 34 (.pack [1]) (.split 35 (.pack [0]) (.split 79 (.pack [7]) (.split 80 (.pack [23]) (.split 87 (.pack [29]) (.zero 14)))))))))))) (.split 31 (.pack [1,28]) (.split 58 (.pack [12,4]) (.split 75 (.pack [3,22]) (.split 77 (.pack [20,9]) (.zero 21)))))) (.split 17 (.split 20 (.pack [16,14]) (.split 32 (.pack [29,5]) (.split 59 (.pack [13,12]) (.split 75 (.pack [21,3]) (.split 76 (.pack [20,9]) (.zero 22)))))) (.split 26 (.split 29 (.split 32 (.pack [22]) (.split 44 (.pack [8]) (.split 71 (.pack [18]) (.split 87 (.pack [28]) (.split 88 (.pack [27]) (.zero 29)))))) (.split 41 (.split 28 (.pack [28]) (.split 44 (.pack [29]) (.split 53 (.pack [7]) (.split 54 (.pack [19]) (.split 56 (.pack [10]) (.split 69 (.pack [27]) (.split 70 (.pack [28]) (.split 73 (.pack [19]) (.split 74 (.pack [19]) (.split 83 (.pack [24]) (.zero 11))))))))))) (.split 68 (.split 7 (.pack [7]) (.split 10 (.pack [10]) (.split 22 (.pack [14]) (.split 49 (.pack [3]) (.split 66 (.pack [25]) (.zero 17)))))) (.split 84 (.pack [12,8]) (.split 85 (.pack [13,25]) (.zero 26)))))) (.split 28 (.split 31 (.pack [21,1]) (.split 43 (.pack [13,10]) (.split 70 (.pack [18,11]) (.split 87 (.pack [29,14]) (.split 89 (.pack [27,6]) (.zero 28)))))) (.split 29 (.split 41 (.pack [29,5]) (.split 68 (.pack [17,29]) (.split 84 (.pack [12,29]) (.split 85 (.pack [13,25]) (.zero 26))))) (.split 41 (.split 68 (.split 7 (.pack [7]) (.split 10 (.pack [10]) (.split 22 (.pack [14]) (.split 49 (.pack [3]) (.split 66 (.pack [25]) (.zero 17)))))) (.split 84 (.pack [12,8]) (.split 85 (.pack [13,25]) (.zero 26)))) (.split 44 (.split 32 (.pack [22,5]) (.split 71 (.pack [18,2]) (.split 87 (.pack [28,14]) (.split 88 (.pack [27,5]) (.zero 29))))) (.split 53 (.split 7 (.split 10 (.pack [10]) (.split 22 (.pack [8]) (.split 49 (.pack [3]) (.split 66 (.pack [25]) (.split 68 (.pack [26]) (.zero 17)))))) (.split 37 (.split 8 (.pack [16]) (.split 10 (.pack [17]) (.split 22 (.pack [17]) (.split 23 (.pack [14]) (.split 51 (.pack [7]) (.split 64 (.pack [16]) (.split 65 (.pack [15]) (.split 69 (.pack [27]) (.split 71 (.pack [29]) (.split 80 (.pack [23]) (.split 82 (.pack [10]) (.split 83 (.pack [24]) (.zero 8))))))))))))) (.split 40 (.pack [10,2]) (.split 51 (.pack [18,2]) (.split 79 (.pack [23,9]) (.zero 7)))))) (.split 54 (.pack [19,10,4]) (.split 56 (.split 10 (.split 7 (.pack [7]) (.split 22 (.pack [14]) (.split 49 (.pack [3]) (.split 66 (.pack [25]) (.split 68 (.pack [26]) (.zero 17)))))) (.split 40 (.split 7 (.pack [17]) (.split 37 (.pack [8]) (.split 51 (.pack [18]) (.split 79 (.pack [23]) (.zero 7))))) (.split 43 (.pack [13,28]) (.split 82 (.split 21 (.pack [23]) (.split 24 (.pack [18]) (.split 36 (.pack [3]) (.split 63 (.pack [16]) (.split 83 (.pack [11]) (.zero 24)))))) (.zero 10))))) (.split 69 (.split 27 (.pack [19,25]) (.split 30 (.pack [20,8]) (.split 42 (.pack [12,8]) (.split 88 (.pack [29,9]) (.split 89 (.pack [28,8]) (.zero 27)))))) (.split 70 (.split 31 (.pack [21,18]) (.split 43 (.pack [10,13]) (.split 87 (.pack [29,14]) (.split 89 (.pack [27,18]) (.zero 28))))) (.split 73 (.pack [19,1,5]) (.split 74 (.split 12 (.pack [18,12]) (.split 15 (.pack [20,14]) (.split 27 (.pack [27,25]) (.zero 19)))) (.split 83 (.split 21 (.pack [23,9]) (.split 24 (.pack [18,25]) (.split 36 (.pack [3,8]) (.split 63 (.split 5 (.pack [8]) (.split 8 .done (.split 20 (.pack [22]) (.split 47 (.pack [1]) (.split 64 (.pack [15]) (.zero 16)))))) (.split 82 (.pack [10,2]) (.zero 24)))))) (.zero 11)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 468 is kernel-checked. -/
theorem checked468 : checkParitySearch 8 (fun q => lane 256 q rows468) 0x875 (allowed468.contains) tree468 0x3fdbef79f6ebfbffdffb7eb 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 468 satisfy the full bottom equations. -/
theorem initial468 : checkSearchInitial 8 90 30 rows468 lambdas468 0x875 0x241086091404002004814 0x2182450024010c12280120 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 468. -/
theorem rhs468 : reconX bottomRColumns 0x241086091404002004814 = 0x2182450024010c12280120 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 468 has a listed outside support. -/
theorem complete468 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x241086091404002004814)
    (hoff : bitCount 90 (outsideMask word 0x241086091404002004814) ≤ 3) :
    outsideMask word 0x241086091404002004814 ∈ allowed468 := by
  exact outside_mem_of_search 8 90 30 rows468 lambdas468 0x875 0x241086091404002004814 0x2182450024010c12280120 3
    bottomEColumns bottomETransposeColumns tree468 allowed468 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial468 checked468
    hw (he.trans rhs468) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 469. -/
noncomputable def rows469 : Nat := (Nat.lor 0xc00040000008009000000000000000000000000000000000000000000000000140002000000400480000000000000000000000000000000000000000000000001800080000010012000000000000000000000000000000000000000000000000300002000000400480000000000000000000000000000000000000000008180000000000c00d880090000000000000000000000000000000000000000002000000a000800000020020000000000000000000000000000000000000000001000000c0004000000100100000000000000000000000000000000000000000008000000c01200000008000000000000000000000000000000000000000000000400000140090000000400000000000000000000000000000000000000000002d8008901880da0814010000000000000000000000000000000000000000000000d00a30008022004c02500000000000000000000000000000000000000000000008000002801200000008000000000000000000000000000000000000000000000080000060012000000080000000000000000000000000000000000000000030184028000200500d300a20000000000000000000000000000000000000000000002000000a004800000020000000000000000000000000000000000000000034182028700900e60d100a3 (Nat.shiftLeft 0x180008000001001200000000000000000000000000000000000000000000000030000200000040048000000000000000000000000000000000000000000000000300010000002002400000000000000000000000000000000000000000000000060000400000080090000000000000000000000000000000000000000000000000c000080000010012000000000000000000000000000000000000000000000000180001000000200240000000000000000000000000000000000000000000000001800080000010012000000000000000000000000000000000000000000000000280004000000800900000000000000000000000000000000000000000000000030000200000040048000000000000000000000000000000000000000000000000600004000000800900000000000000000000000000000000000000000000280062001a00800a4032800 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 469. -/
noncomputable def lambdas469 : Nat := (Nat.lor 0x8000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000180000000000000008000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000124002000000000000002000000000000000000000000000000000000000000000c0040000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000018001600000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000184016800000000000001 (Nat.shiftLeft 0x1000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000010006000000000004000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 469. -/
noncomputable def allowed469 : List Nat := [0x480080000,0x10000a00000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 469. -/
noncomputable def tree469 : ParitySearchTree := (.split 11 (.split 8 (.pack [13,8]) (.split 23 (.pack [8,11]) (.split 50 (.pack [3,8]) (.split 66 (.pack [14,8]) (.split 67 (.pack [8,2]) (.zero 15)))))) (.split 13 (.split 1 (.pack [1,5]) (.split 43 (.pack [7,2]) (.split 57 (.pack [18,5]) (.split 59 (.pack [20,9]) (.split 85 (.pack [24,23]) (.zero 10)))))) (.split 16 (.split 19 (.split 0 (.pack [9]) (.split 3 (.pack [12]) (.split 15 (.pack [17]) (.split 20 (.pack [13]) (.split 22 (.pack [14]) (.split 23 (.pack [15]) (.split 34 (.pack [1]) (.split 35 (.pack [6]) (.split 79 (.pack [4]) (.split 80 (.pack [21]) (.split 87 (.pack [26]) (.zero 11)))))))))))) (.split 31 (.split 1 (.pack [10]) (.split 34 (.pack [11]) (.split 45 (.pack [12]) (.split 47 (.pack [13]) (.split 73 (.pack [17]) (.zero 1)))))) (.split 58 (.split 0 (.pack [11]) (.split 12 (.pack [17]) (.split 42 (.pack [25]) (.split 59 (.pack [10]) (.split 84 (.pack [24]) (.zero 9)))))) (.split 75 (.pack [3,20]) (.split 77 (.pack [18,6]) (.zero 19)))))) (.split 17 (.split 20 (.pack [13,11]) (.split 32 (.split 29 (.pack [24]) (.split 44 (.pack [8]) (.split 71 (.pack [5]) (.split 87 (.pack [11]) (.split 88 (.pack [25]) (.zero 26)))))) (.split 59 (.pack [10,9]) (.split 75 (.pack [19,3]) (.split 76 (.pack [18,6]) (.zero 20)))))) (.split 26 (.split 29 (.split 32 (.pack [20]) (.split 44 (.pack [8]) (.split 71 (.pack [16]) (.split 87 (.pack [11]) (.split 88 (.pack [25]) (.zero 26)))))) (.split 41 (.pack [8,2]) (.split 68 (.split 7 (.pack [4]) (.split 10 (.pack [7]) (.split 22 (.pack [11]) (.split 49 (.pack [3]) (.split 66 (.pack [15]) (.zero 14)))))) (.split 84 (.pack [9,5]) (.split 85 (.pack [10,23]) (.zero 24)))))) (.split 29 (.split 41 (.pack [8,2]) (.split 68 (.pack [14,26]) (.split 84 (.pack [9,26]) (.split 85 (.pack [10,23]) (.zero 24))))) (.split 31 (.split 19 (.split 1 (.pack [10]) (.split 34 .done (.split 45 (.pack [12]) (.split 47 (.pack [13]) (.split 73 (.pack [17]) (.zero 1)))))) (.split 58 (.pack [1,9]) (.split 75 (.pack [20,3]) (.split 77 (.pack [1,18]) (.zero 19))))) (.split 43 (.split 1 (.pack [1,7]) (.split 57 (.pack [18,7]) (.split 59 (.pack [20,7]) (.split 85 (.pack [24,7]) (.zero 10))))) (.split 53 (.split 7 (.split 10 (.pack [7]) (.split 22 (.pack [11]) (.split 49 (.pack [3]) (.split 66 (.pack [15]) (.split 68 (.pack [24]) (.zero 14)))))) (.split 37 (.split 8 (.pack [15]) (.split 10 (.pack [14]) (.split 22 (.pack [14]) (.split 23 (.pack [15]) (.split 41 (.pack [24]) (.split 51 (.pack [4]) (.split 64 (.pack [13]) (.split 65 (.pack [12]) (.split 69 (.pack [25]) (.split 71 (.pack [26]) (.split 80 (.pack [21]) (.split 82 (.pack [7]) (.split 83 (.pack [8]) (.zero 5)))))))))))))) (.split 40 (.pack [7,2]) (.split 51 (.split 8 (.pack [15]) (.split 10 (.pack [7]) (.split 22 (.pack [14]) (.split 23 (.pack [15]) (.split 41 (.pack [24]) (.split 64 (.pack [13]) (.split 65 (.pack [12]) (.split 69 (.pack [25]) (.split 71 (.pack [26]) (.split 80 (.pack [21]) (.split 82 (.pack [7]) (.split 83 (.pack [8]) (.zero 5))))))))))))) (.split 79 (.pack [21,6]) (.zero 4)))))) (.split 55 (.split 41 (.pack [24,5]) (.split 44 (.split 32 (.pack [20]) (.split 71 (.pack [5]) (.split 87 (.pack [16]) (.split 88 (.pack [25]) (.zero 26))))) (.split 54 (.pack [7,17]) (.split 83 (.split 21 (.pack [21]) (.split 24 (.pack [23]) (.split 36 (.pack [3]) (.split 63 (.pack [13]) (.split 82 (.pack [7]) (.zero 22)))))) (.zero 8))))) (.split 56 (.split 10 (.split 7 (.pack [4]) (.split 22 (.pack [11]) (.split 49 (.pack [3]) (.split 66 (.pack [15]) (.split 68 (.pack [24]) (.zero 14)))))) (.split 40 (.split 7 (.pack [14]) (.split 37 (.pack [5]) (.split 51 (.pack [5]) (.split 79 (.pack [21]) (.zero 4))))) (.split 54 (.pack [8,17]) (.split 82 (.split 21 (.pack [21]) (.split 24 (.pack [23]) (.split 36 (.pack [3]) (.split 63 (.pack [13]) (.split 83 (.pack [8]) (.zero 22)))))) (.zero 7))))) (.split 69 (.split 27 (.pack [17,23]) (.split 30 (.pack [18,5]) (.split 42 (.pack [9,5]) (.split 88 (.split 32 (.pack [20]) (.split 44 (.pack [8]) (.split 71 .done (.split 87 (.pack [16]) (.zero 26))))) (.split 89 (.pack [16,5]) (.zero 25)))))) (.split 73 (.split 1 (.pack [10,17]) (.split 34 (.pack [17,0]) (.split 45 (.pack [12,17]) (.split 47 (.pack [13,17]) (.zero 1))))) (.split 74 (.split 12 (.split 0 (.pack [11]) (.split 42 (.pack [25]) (.split 58 (.pack [19]) (.split 59 (.pack [10]) (.split 84 (.pack [24]) (.zero 9)))))) (.split 15 (.pack [18,11]) (.split 27 (.pack [25,23]) (.split 54 (.pack [7,8]) (.zero 17))))) (.split 87 (.split 32 (.split 20 (.pack [13]) (.split 59 (.pack [10]) (.split 75 (.pack [19]) (.split 76 (.pack [18]) (.zero 20))))) (.split 44 (.pack [8,11]) (.split 71 (.split 0 (.pack [9]) (.split 3 (.pack [12]) (.split 15 (.pack [17]) (.split 19 (.pack [19]) (.split 20 (.pack [20]) (.split 22 (.pack [14]) (.split 23 (.pack [15]) (.split 34 (.pack [1]) (.split 35 (.pack [5]) (.split 79 (.pack [4]) (.split 80 (.pack [21]) (.zero 11)))))))))))) (.split 88 (.pack [25,11]) (.zero 26))))) (.split 89 (.split 27 (.pack [17,23]) (.split 30 (.split 15 (.pack [17]) (.split 18 (.pack [12]) (.split 57 (.pack [10]) (.split 76 (.pack [20]) (.split 77 (.pack [19]) (.zero 18)))))) (.split 42 (.split 0 (.pack [11]) (.split 12 (.pack [17]) (.split 58 (.pack [19]) (.split 59 (.pack [10]) (.split 84 (.pack [24]) (.zero 9)))))) (.split 88 (.split 32 (.pack [20]) (.split 44 (.pack [8]) (.split 71 (.pack [2]) (.zero 26)))) (.zero 25))))) (.zero 16)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 469 is kernel-checked. -/
theorem checked469 : checkParitySearch 8 (fun q => lane 256 q rows469) 0x10045 (allowed469.contains) tree469 0x3fdbebf9feebfbfedffbdeb 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 469 satisfy the full bottom equations. -/
theorem initial469 : checkSearchInitial 8 90 27 rows469 lambdas469 0x10045 0x241406011404012004214 0x10180450024080c02280120 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 469. -/
theorem rhs469 : reconX bottomRColumns 0x241406011404012004214 = 0x10180450024080c02280120 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 469 has a listed outside support. -/
theorem complete469 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x241406011404012004214)
    (hoff : bitCount 90 (outsideMask word 0x241406011404012004214) ≤ 3) :
    outsideMask word 0x241406011404012004214 ∈ allowed469 := by
  exact outside_mem_of_search 8 90 27 rows469 lambdas469 0x10045 0x241406011404012004214 0x10180450024080c02280120 3
    bottomEColumns bottomETransposeColumns tree469 allowed469 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial469 checked469
    hw (he.trans rhs469) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 88 matches a certified search. -/
theorem matches22000 : records22000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → (r.beta = 0x2402803006800c2884040 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed465) ∨ (r.beta = 0x241012510280080802105 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed466))) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 88. -/
theorem chunk_complete22000 (r : Fiber) (hr : r ∈ records22000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches22000) r hr)) hweight
  rcases h with h0 | h1
  · exact search_census_transfer r 0x2402803006800c2884040 3 allowed465 complete465 h0 word hw he hoff
  · exact search_census_transfer r 0x241012510280080802105 3 allowed466 complete466 h1 word hw he hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 89 matches a certified search. -/
theorem matches22250 : records22250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → (r.beta = 0x241016081404000004954 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed467) ∨ (r.beta = 0x241086091404002004814 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed468) ∨ (r.beta = 0x241406011404012004214 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed469))) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 89. -/
theorem chunk_complete22250 (r : Fiber) (hr : r ∈ records22250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches22250) r hr)) hweight
  rcases h with h0 | h1 | h2
  · exact search_census_transfer r 0x241016081404000004954 3 allowed467 complete467 h0 word hw he hoff
  · exact search_census_transfer r 0x241086091404002004814 3 allowed468 complete468 h1 word hw he hoff
  · exact search_census_transfer r 0x241406011404012004214 3 allowed469 complete469 h2 word hw he hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 90 matches a certified search. -/
theorem matches22500 : records22500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 90. -/
theorem chunk_complete22500 (r : Fiber) (hr : r ∈ records22500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches22500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 91 matches a certified search. -/
theorem matches22750 : records22750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 91. -/
theorem chunk_complete22750 (r : Fiber) (hr : r ∈ records22750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches22750) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 92 matches a certified search. -/
theorem matches23000 : records23000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 92. -/
theorem chunk_complete23000 (r : Fiber) (hr : r ∈ records23000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches23000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 93 matches a certified search. -/
theorem matches23250 : records23250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 93. -/
theorem chunk_complete23250 (r : Fiber) (hr : r ∈ records23250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches23250) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 94 matches a certified search. -/
theorem matches23500 : records23500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 94. -/
theorem chunk_complete23500 (r : Fiber) (hr : r ∈ records23500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches23500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 95 matches a certified search. -/
theorem matches23750 : records23750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 95. -/
theorem chunk_complete23750 (r : Fiber) (hr : r ∈ records23750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches23750) r hr)) hweight
  exact False.elim h

#print axioms chunk_complete22000
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch

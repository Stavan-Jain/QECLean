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
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestFastPart12

noncomputable section
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch
open F2Mask PackedDigits FiberData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed projected parity rows for high-cap case 470. -/
noncomputable def rows470 : Nat := (Nat.lor 0x28000400000080090000000000000000000000000000000000000000001000000500000000001001200000000000000000000000000000000000000000040000006001000000040040000000000000000000000000000000000000000002000000a000800000020020000000000000000000000000000000000000000029000c25c08847006f2830c00000000000000000000000000000000000000000008000000c01200000008000000000000000000000000000000000000000000000800c0808809103823e6000000000000000000000000000000000000000000000800c2804804d03ca3e000000000000000000000000000000000000000000000010000001802400000010000000000000000000000000000000000000000000000800000280120000000800000000000000000000000000000000000000000000040000030009000000040000000000000000000000000000000000000000000602012000180b80eb0058000000000000000000000000000000000000000000261500a100180d00e3a08140000000000000000000000000000000000000000000008180000001200c00d880000000000000000000000000000000000000000000002c0804840790ee4824c00000000000000000000000000000000000000000201420290000000805e014e (Nat.shiftLeft 0x18000800000100120000000000000000000000000000000000000000000000002800040000008009000000000000000000000000000000000000000000000000300002000000400480000000000000000000000000000000000000000000000003000100000020024000000000000000000000000000000000000000000000000500008000001001200000000000000000000000000000000000000000000000000c0004000000800900000000000000000000000000000000000000000000000018000100000020024000000000000000000000000000000000000000000000000180008000001001200000000000000000000000000000000000000000000000028000400000080090000000000000000000000000000000000000000000000003000020000004004800000000000000000000000000000000000000000000000006000200000040048000000000000000000000000000000000000000000000000a000100000020024000000000000000000000000000000000000000000000000180001000000200240 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Dual witnesses for the projected rows for high-cap case 470. -/
noncomputable def lambdas470 : Nat := (Nat.lor 0x800000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000e00225000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000002072000000000000004000000000000000000000000000000000000000000000a072000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000001e000a00000000000000200000000000000000000000000000000000000000001e8012400000000000001000000000000000000000000000000000000000000000001800000000000000080000000000000000000000000000000000000000000e01208000000000000004000000000000000000000000000000000000000000008002c000000000000002 (Nat.shiftLeft 0x100000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exact seed outside supports for high-cap case 470. -/
noncomputable def allowed470 : List Nat := [0x8000000240,0x8000c00000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for high-cap case 470. -/
noncomputable def tree470 : ParitySearchTree := (.split 1 (.split 13 (.pack [17,14]) (.split 43 (.pack [14,27]) (.split 57 (.pack [19,13]) (.split 59 (.pack [21,14]) (.split 85 (.pack [25,14]) (.zero 12)))))) (.split 2 (.split 14 (.split 11 (.pack [10]) (.split 26 (.pack [25]) (.split 53 (.pack [5]) (.split 69 (.pack [17]) (.split 70 (.pack [27]) (.zero 18)))))) (.split 44 (.pack [10,28]) (.split 57 (.pack [12,19]) (.split 58 (.pack [20,1]) (.split 86 (.split 25 (.pack [17]) (.split 28 (.pack [27]) (.split 40 (.pack [6]) (.split 67 (.pack [16]) (.split 84 (.pack [25]) (.zero 24)))))) (.zero 13)))))) (.split 3 (.split 7 (.pack [15,6]) (.split 8 (.split 38 (.pack [0]) (.split 41 (.pack [10]) (.split 51 (.pack [6]) (.split 52 (.pack [17]) (.split 80 (.pack [22]) (.zero 7)))))) (.split 10 (.split 13 (.pack [12]) (.split 25 (.pack [24]) (.split 52 (.pack [7]) (.split 69 (.pack [18]) (.split 71 (.pack [28]) (.zero 17)))))) (.split 11 (.pack [18,10]) (.split 22 (.split 6 (.pack [16]) (.split 17 (.pack [21]) (.split 18 (.pack [19]) (.split 19 (.pack [15]) (.split 20 (.pack [21]) (.split 31 (.pack [20]) (.split 60 (.pack [22]) (.split 63 (.pack [15]) (.split 65 (.pack [15]) (.split 73 (.pack [4]) (.split 78 (.pack [5]) (.split 80 (.pack [22]) (.split 89 (.pack [27]) (.zero 0)))))))))))))) (.split 23 (.pack [23,9]) (.split 33 (.split 18 (.pack [19]) (.split 21 (.pack [16]) (.split 60 (.pack [14]) (.split 79 (.pack [6]) (.split 80 (.pack [7]) (.zero 22)))))) (.split 36 (.pack [5,11]) (.split 67 (.pack [16,24]) (.split 68 (.pack [16,25]) (.split 75 (.pack [21,20]) (.zero 2)))))))))))) (.split 6 (.split 9 (.split 36 (.pack [2]) (.split 39 .done (.split 52 (.pack [17]) (.split 53 (.pack [18]) (.split 78 (.pack [23]) (.zero 5)))))) (.split 21 (.pack [5,22]) (.split 48 (.split 36 (.pack [2]) (.split 39 (.pack [4]) (.split 52 (.pack [17]) (.split 53 (.pack [18]) (.split 78 (.pack [23]) (.zero 5)))))) (.split 67 (.pack [5,24]) (.split 68 (.pack [5,25]) (.zero 16)))))) (.split 8 (.split 38 (.split 7 (.pack [15]) (.split 10 (.pack [17]) (.split 11 (.pack [18]) (.split 22 (.pack [0]) (.split 23 (.pack [23]) (.split 33 (.pack [22]) (.split 36 (.pack [5]) (.split 67 (.pack [16]) (.split 68 (.pack [16]) (.split 75 (.pack [21]) (.zero 2))))))))))) (.split 41 (.pack [10,25]) (.split 51 (.pack [6,3]) (.split 52 (.pack [5,17]) (.split 80 (.split 18 (.pack [19]) (.split 21 (.pack [16]) (.split 33 (.pack [0]) (.split 60 (.pack [14]) (.split 79 (.pack [6]) (.zero 22)))))) (.zero 7)))))) (.split 17 (.split 20 (.split 23 (.pack [2]) (.split 35 (.pack [0]) (.split 62 (.pack [14]) (.split 78 (.pack [5]) (.split 79 (.pack [6]) (.zero 23)))))) (.split 32 (.pack [28,4]) (.split 59 (.pack [12,11]) (.split 75 (.pack [20,2]) (.split 76 (.pack [19,3]) (.zero 21)))))) (.split 18 (.split 15 (.split 21 (.pack [16]) (.split 33 (.pack [2]) (.split 60 (.pack [14]) (.split 79 (.pack [6]) (.split 80 (.pack [7]) (.zero 22)))))) (.split 30 (.pack [22,26]) (.split 57 (.pack [12,13]) (.split 76 (.pack [21,22]) (.split 77 (.pack [20,22]) (.zero 19)))))) (.split 19 (.split 4 (.pack [14,4]) (.split 7 (.pack [20,6]) (.split 46 (.pack [20,1]) (.split 63 (.pack [20,1]) (.split 65 (.pack [20,3]) (.zero 15)))))) (.split 20 (.pack [21,23,9]) (.split 22 (.split 7 (.pack [15,6]) (.split 10 (.split 13 (.pack [12]) (.split 25 (.pack [24]) (.split 52 (.pack [5]) (.split 69 (.pack [18]) (.split 71 (.pack [28]) (.zero 17)))))) (.split 11 (.pack [18,10]) (.split 23 (.pack [23,9]) (.split 33 (.split 21 (.pack [16]) (.split 60 (.pack [14]) (.split 79 (.pack [23]) (.split 80 (.pack [7]) (.zero 22))))) (.split 36 (.pack [5,11]) (.split 67 (.pack [16,24]) (.split 68 (.pack [16,25]) (.split 75 (.pack [21,20]) (.zero 2)))))))))) (.split 31 (.split 16 (.pack [14,27]) (.split 58 (.pack [13,27]) (.split 75 (.pack [21,27]) (.split 77 (.pack [19,27]) (.zero 20))))) (.split 60 (.split 21 (.pack [16,14]) (.split 33 (.pack [14,2]) (.split 79 (.pack [23,6]) (.split 80 (.pack [7,14]) (.zero 22))))) (.split 63 (.split 4 (.pack [14,1]) (.split 7 (.pack [6,2]) (.split 46 (.split 10 (.pack [17]) (.split 21 (.pack [22]) (.split 23 (.pack [23]) (.split 25 (.pack [17]) (.split 26 (.pack [18]) (.split 27 (.pack [26]) (.split 35 (.pack [23]) (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 39 (.pack [5]) (.split 47 .done (.split 48 (.pack [16]) (.split 65 (.zero 15) (.split 68 (.pack [16]) (.split 77 (.pack [20]) (.split 85 (.pack [25]) (.split 86 (.pack [13]) (.zero 4)))))))))))))))))) (.split 65 (.pack [0,8]) (.zero 15))))) (.split 65 (.split 4 (.pack [14,3]) (.split 7 (.pack [6,2]) (.split 46 (.split 9 (.pack [16]) (.split 15 (.pack [19]) (.split 21 (.pack [16]) (.split 23 (.pack [23]) (.split 25 (.pack [17]) (.split 26 (.pack [18]) (.split 27 (.pack [26]) (.split 32 (.pack [21]) (.split 35 (.pack [23]) (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 38 (.pack [7]) (.split 51 (.pack [6]) (.split 54 (.pack [10]) (.split 70 (.pack [18]) (.split 71 (.pack [17]) (.split 73 (.pack [0]) (.zero 1)))))))))))))))))) (.zero 15)))) (.split 73 (.split 9 (.split 21 (.pack [22]) (.split 48 (.pack [8]) (.split 67 (.pack [24]) (.split 68 (.pack [25]) (.zero 16))))) (.split 15 (.split 30 (.pack [26]) (.split 57 (.pack [12]) (.split 76 (.pack [21]) (.split 77 (.pack [20]) (.zero 19))))) (.split 21 (.pack [16,22]) (.split 23 (.pack [23,2]) (.split 25 (.pack [17,24]) (.split 26 (.pack [18,25]) (.split 27 (.split 30 (.pack [19]) (.split 42 (.pack [8]) (.split 69 (.pack [18]) (.split 88 (.pack [14]) (.split 89 (.pack [0]) (.zero 26)))))) (.split 32 (.pack [21,28]) (.split 35 (.pack [23,8]) (.split 36 (.pack [5,2]) (.split 37 (.pack [6,3]) (.split 38 (.pack [7,4]) (.split 46 (.pack [15,11]) (.split 51 (.pack [7,6]) (.split 54 (.pack [10,4]) (.split 70 (.pack [18,27]) (.split 71 (.pack [17,28]) (.zero 1)))))))))))))))))) (.split 78 (.split 36 (.pack [23,3]) (.split 39 (.pack [23,3]) (.split 52 (.pack [23,7]) (.split 53 (.pack [23,18]) (.zero 5))))) (.split 80 (.split 21 (.pack [7,16]) (.split 33 (.pack [7,2]) (.split 79 (.pack [23,7]) (.zero 22)))) (.split 89 (.split 28 (.pack [24,26]) (.split 43 (.pack [12,26]) (.split 70 (.split 11 (.pack [10]) (.split 14 (.pack [13]) (.split 26 (.pack [25]) (.split 53 (.pack [5]) (.split 69 (.pack [17]) (.zero 18)))))) (.split 87 (.split 27 (.pack [28]) (.split 30 (.pack [19]) (.split 42 (.pack [28]) (.split 69 (.pack [18]) (.split 88 (.pack [14]) (.zero 26)))))) (.zero 27))))) (.zero 0)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every search branch for high-cap case 470 is kernel-checked. -/
theorem checked470 : checkParitySearch 8 (fun q => lane 256 q rows470) 0xb19 (allowed470.contains) tree470 0x3f9fafadef9dffbfeffefde 0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Initial projected duals for high-cap case 470 satisfy the full bottom equations. -/
theorem initial470 : checkSearchInitial 8 90 29 rows470 lambdas470 0xb19 0x605052106200401001021 0x148418800240a420c40012 bottomETransposeColumns = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The actual bottom carry gives the certified right-hand side for case 470. -/
theorem rhs470 : reconX bottomRColumns 0x605052106200401001021 = 0x148418800240a420c40012 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every sufficiently light solution in high-cap case 470 has a listed outside support. -/
theorem complete470 {word : Nat} (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns 0x605052106200401001021)
    (hoff : bitCount 90 (outsideMask word 0x605052106200401001021) ≤ 3) :
    outsideMask word 0x605052106200401001021 ∈ allowed470 := by
  exact outside_mem_of_search 8 90 29 rows470 lambdas470 0xb19 0x605052106200401001021 0x148418800240a420c40012 3
    bottomEColumns bottomETransposeColumns tree470 allowed470 (by decide)
    (fun lam v _ _ => bottomETranspose_parityFold lam v) transpose_bounded initial470 checked470
    hw (he.trans rhs470) hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 96 matches a certified search. -/
theorem matches24000 : records24000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 96. -/
theorem chunk_complete24000 (r : Fiber) (hr : r ∈ records24000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches24000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 97 matches a certified search. -/
theorem matches24250 : records24250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 97. -/
theorem chunk_complete24250 (r : Fiber) (hr : r ∈ records24250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches24250) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 98 matches a certified search. -/
theorem matches24500 : records24500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 98. -/
theorem chunk_complete24500 (r : Fiber) (hr : r ∈ records24500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches24500) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 99 matches a certified search. -/
theorem matches24750 : records24750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 99. -/
theorem chunk_complete24750 (r : Fiber) (hr : r ∈ records24750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches24750) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 100 matches a certified search. -/
theorem matches25000 : records25000.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 100. -/
theorem chunk_complete25000 (r : Fiber) (hr : r ∈ records25000)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches25000) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 101 matches a certified search. -/
theorem matches25250 : records25250.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 101. -/
theorem chunk_complete25250 (r : Fiber) (hr : r ∈ records25250)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches25250) r hr)) hweight
  exact False.elim h

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 102 matches a certified search. -/
theorem matches25500 : records25500.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → (r.beta = 0x605052106200401001021 ∧ outsideBudget r = 3 ∧ r.seeds.map Seed.off = allowed470))) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 102. -/
theorem chunk_complete25500 (r : Fiber) (hr : r ∈ records25500)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches25500) r hr)) hweight
  exact search_census_transfer r 0x605052106200401001021 3 allowed470 complete470 h word hw he hoff

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every high-cap record in canonical chunk 103 matches a certified search. -/
theorem matches25750 : records25750.all (fun r => decide (
    (r.weight = 16 ∨ r.weight = 14) → False)) = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The checked searches give the exact seed-support list for canonical chunk 103. -/
theorem chunk_complete25750 (r : Fiber) (hr : r ∈ records25750)
    (hweight : r.weight = 16 ∨ r.weight = 14) (word : Nat) (_hw : word < 2^90)
    (_he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (_hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have h := (of_decide_eq_true ((List.all_eq_true.mp matches25750) r hr)) hweight
  exact False.elim h

#print axioms chunk_complete24000
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest.HighSearch

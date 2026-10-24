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

import QEC.Stabilizer.Framework.Homological.Certificate.SearchTree

noncomputable section

set_option maxRecDepth 1000000
namespace Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 304. -/
noncomputable def rows304 : Nat := 0xc0000000000000004000000800900000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000000000000000000000038000007007e000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000030000000030000006006c00c00d8000000000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 304. -/
noncomputable def allowed304 : List Nat := [0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 304. -/
noncomputable def tree304 : ParitySearchTree := (.split 57 (.pack [3]) (.split 58 (.pack [4]) (.split 59 (.pack [5]) (.split 60 (.pack [2]) (.split 61 .done (.split 62 .done (.split 72 (.pack [9]) (.split 73 (.pack [7]) (.split 74 (.pack [8]) (.split 99 (.pack [0]) (.split 100 (.pack [1]) (.split 101 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 304. -/
theorem checked304 : checkParitySearch 8 (fun q => (rows304 >>> (256*q)) &&& (2^256-1)) 0x44 (allowed304.contains) tree304 0xfff03fe3fdf7fffff7fffffefffffffffff9dff3ffdbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 305. -/
noncomputable def rows305 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e00000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 305. -/
noncomputable def allowed305 : List Nat := [0x1000000000000000,0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 305. -/
noncomputable def tree305 : ParitySearchTree := (.split 57 (.pack [3]) (.split 58 (.pack [4]) (.split 59 (.pack [5]) (.split 60 .done (.split 61 .done (.split 62 .done (.split 72 (.pack [7]) (.split 73 (.pack [8]) (.split 74 (.pack [9]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 305. -/
theorem checked305 : checkParitySearch 8 (fun q => (rows305 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed305.contains) tree305 0xfff03fd5ff9fffffffffffffffffffff99ff1ffcfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 306. -/
noncomputable def rows306 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e00000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 306. -/
noncomputable def allowed306 : List Nat := [0x1000000000000000,0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 306. -/
noncomputable def tree306 : ParitySearchTree := (.split 57 (.pack [3]) (.split 58 (.pack [4]) (.split 59 (.pack [5]) (.split 60 .done (.split 61 .done (.split 62 .done (.split 72 (.pack [7]) (.split 73 (.pack [8]) (.split 74 (.pack [9]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 306. -/
theorem checked306 : checkParitySearch 8 (fun q => (rows306 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed306.contains) tree306 0xfff03fceffafffffffffffffffffffff95ff1ffd7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 307. -/
noncomputable def rows307 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 307. -/
noncomputable def allowed307 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 307. -/
noncomputable def tree307 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 3 .done (.split 4 .done (.split 5 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 307. -/
theorem checked307 : checkParitySearch 8 (fun q => (rows307 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed307.contains) tree307 0xffeffffffffffffff11fe3bfe7fc3fff7fffffffffe7f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 308. -/
noncomputable def rows308 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 308. -/
noncomputable def allowed308 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 308. -/
noncomputable def tree308 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 3 .done (.split 4 .done (.split 5 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 308. -/
theorem checked308 : checkParitySearch 8 (fun q => (rows308 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed308.contains) tree308 0xffefffffffffffffea1fd3bfe7fa3fff7fffffffffebf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 309. -/
noncomputable def rows309 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 309. -/
noncomputable def allowed309 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 309. -/
noncomputable def tree309 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 3 .done (.split 4 .done (.split 5 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 309. -/
theorem checked309 : checkParitySearch 8 (fun q => (rows309 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed309.contains) tree309 0xffefffffffffffffdc1fb3bfe7f63fff7ffffffffff3f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 310. -/
noncomputable def rows310 : Nat := 0x8000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000001c0000000000000000000000000000e00fc0000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 310. -/
noncomputable def allowed310 : List Nat := [0x40,0x80,0x100]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 310. -/
noncomputable def tree310 : ParitySearchTree := (.split 6 .done (.split 7 .done (.split 8 .done (.split 9 (.pack [0]) (.split 10 (.pack [1]) (.split 11 (.pack [2]) (.split 21 (.pack [4]) (.split 22 (.pack [5]) (.split 23 (.pack [6]) (.split 138 (.pack [8]) (.split 139 (.pack [9]) (.split 140 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 310. -/
theorem checked310 : checkParitySearch 8 (fun q => (rows310 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed310.contains) tree310 0xffefffffffffffffc1df8fbfe7f1bfff7ffffffffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 311. -/
noncomputable def rows311 : Nat := 0x2000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 311. -/
noncomputable def allowed311 : List Nat := [0x1,0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 311. -/
noncomputable def tree311 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 .done (.split 3 (.pack [0]) (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 1)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 311. -/
theorem checked311 : checkParitySearch 8 (fun q => (rows311 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed311.contains) tree311 0xffeffffffffffffdbf07fc7fe77fc7ff7ffffffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 312. -/
noncomputable def rows312 : Nat := 0x2000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 312. -/
noncomputable def allowed312 : List Nat := [0x1,0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 312. -/
noncomputable def tree312 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 .done (.split 3 (.pack [0]) (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 15 (.pack [5]) (.split 16 (.pack [4]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 1)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 312. -/
theorem checked312 : checkParitySearch 8 (fun q => (rows312 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed312.contains) tree312 0xffeffffffffffffb7f0bfc7fe6ffc7ff7ffffffffafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 313. -/
noncomputable def rows313 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 313. -/
noncomputable def allowed313 : List Nat := [0x1,0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 313. -/
noncomputable def tree313 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 .done (.split 3 (.pack [0]) (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [4]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 1)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 313. -/
theorem checked313 : checkParitySearch 8 (fun q => (rows313 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed313.contains) tree313 0xffeffffffffffff6ff13fc7fe5ffc7ff7ffffffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 314. -/
noncomputable def rows314 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000038000000000000000007007000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 314. -/
noncomputable def allowed314 : List Nat := [0x1,0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 314. -/
noncomputable def tree314 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 .done (.split 12 (.pack [4]) (.split 13 (.pack [5]) (.split 14 (.pack [6]) (.split 87 (.pack [0]) (.split 88 (.pack [1]) (.split 89 (.pack [2]) (.split 129 (.pack [8]) (.split 130 (.pack [9]) (.split 131 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 314. -/
theorem checked314 : checkParitySearch 8 (fun q => (rows314 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed314.contains) tree314 0xffefffffffffffedff23fc7fe3ffc7ff7fffffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 315. -/
noncomputable def rows315 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f8000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 315. -/
noncomputable def allowed315 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 315. -/
noncomputable def tree315 : ParitySearchTree := (.split 3 .done (.split 4 .done (.split 5 .done (.split 6 (.pack [0]) (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 18 (.pack [4]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 135 (.pack [8]) (.split 136 (.pack [9]) (.split 137 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 315. -/
theorem checked315 : checkParitySearch 8 (fun q => (rows315 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed315.contains) tree315 0xffefffffffffffedf83ff3bfe3fe3fff7fffffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 316. -/
noncomputable def rows316 : Nat := (Nat.lor 0x500000000000000040000008009000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000001000000c002400000000000000000080000000000000000000000a00a000024008004000500c81c50120000000120140000000000000000000004000a00c004004004800100280870250090000020000000000000000000000004a00000c004002004000500e0085037009000002003 (Nat.shiftLeft 0xc00000000000000040000008009000000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000003000000000000000800000100120000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 316. -/
noncomputable def allowed316 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 316. -/
noncomputable def tree316 : ParitySearchTree := (.split 2 .done (.split 4 (.pack [5]) (.split 13 (.pack [6]) (.split 16 (.pack [7]) (.split 49 (.pack [13]) (.split 52 (.pack [15]) (.split 60 (.pack [17]) (.split 62 (.pack [18]) (.split 66 (.pack [19]) (.split 67 (.pack [15]) (.split 68 (.pack [16]) (.split 75 (.pack [20]) (.split 78 (.pack [3]) (.split 79 (.pack [0]) (.split 88 (.pack [4]) (.split 90 (.pack [0]) (.split 106 (.pack [1]) (.split 119 (.pack [7]) (.split 130 (.pack [10]) (.split 133 (.pack [11]) (.split 153 (.pack [8]) (.split 155 (.pack [9]) (.split 165 (.pack [12]) (.split 167 (.pack [14]) (.zero 2)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 316. -/
theorem checked316 : checkParitySearch 8 (fun q => (rows316 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed316.contains) tree316 0xffefffffffffffdf7f4bfc7feeffc7ff7fffffffd2fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 317. -/
noncomputable def rows317 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000100000050000000000000000000000800900000000000000000000000006005000000004000c002008801300900000000000200000000000000000000002000c00c00000800800080020128001009000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 317. -/
noncomputable def allowed317 : List Nat := [0x20,0x80000000000000000000,0x200000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 317. -/
noncomputable def tree317 : ParitySearchTree := (.split 5 .done (.split 52 (.pack [6]) (.split 55 (.pack [9]) (.split 64 (.pack [6]) (.split 65 (.pack [7]) (.split 68 (.pack [8]) (.split 79 .done (.split 83 (.pack [10]) (.split 93 .done (.split 106 .done (.split 107 (.pack [0]) (.split 122 (.pack [2]) (.split 156 (.pack [8]) (.split 158 (.pack [3]) (.split 169 (.pack [4]) (.split 170 (.pack [5]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 317. -/
theorem checked317 : checkParitySearch 8 (fun q => (rows317 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed317.contains) tree317 0xffefffffffffffdf7cd7fbbfeeff3fff7fffffffd2fe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 318. -/
noncomputable def rows318 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006006c00000000000200240040000041000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000280370050060000000000000000001400d018f000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000020034001006600a004800000000001000801840000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 318. -/
noncomputable def allowed318 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 318. -/
noncomputable def tree318 : ParitySearchTree := (.split 2 .done (.split 7 (.pack [2]) (.split 8 (.pack [3]) (.split 19 (.pack [6]) (.split 32 (.pack [8]) (.split 79 (.pack [4]) (.split 82 (.pack [2]) (.split 93 (.pack [12]) (.split 95 (.pack [0]) (.split 105 (.pack [12]) (.split 106 (.pack [4]) (.split 109 (.pack [13]) (.split 110 (.pack [5]) (.split 120 (.pack [0]) (.split 134 (.pack [7]) (.split 136 (.pack [10]) (.split 137 (.pack [9]) (.split 149 (.pack [11]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 318. -/
theorem checked318 : checkParitySearch 8 (fun q => (rows318 >>> (256*q)) &&& (2^256-1)) 0x12 (allowed318.contains) tree318 0xffefffffffffffdbfe63fe7fefff87ff7fffffffd7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 319. -/
noncomputable def rows319 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000100000050000000000000000000000800900000000000000000000000006005000000004000c002008801300900000000000200000000000000000000002000c00c00000800800080020128001009000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 319. -/
noncomputable def allowed319 : List Nat := [0x20,0x80000000000000000000,0x200000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 319. -/
noncomputable def tree319 : ParitySearchTree := (.split 5 .done (.split 52 (.pack [6]) (.split 55 (.pack [9]) (.split 64 (.pack [6]) (.split 65 (.pack [7]) (.split 68 (.pack [8]) (.split 79 .done (.split 83 (.pack [10]) (.split 93 .done (.split 106 .done (.split 107 (.pack [0]) (.split 122 (.pack [2]) (.split 156 (.pack [8]) (.split 158 (.pack [3]) (.split 169 (.pack [4]) (.split 170 (.pack [5]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 319. -/
theorem checked319 : checkParitySearch 8 (fun q => (rows319 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed319.contains) tree319 0xffefffffffffffdbf5dfebbfeffd3fff7fffffffd7e67 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 320. -/
noncomputable def rows320 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000100000050000000000000000000000800900000000000000000000000006005000000004000c002008801300900000000000200000000000000000000002000c00c00000800800080020128001009000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 320. -/
noncomputable def allowed320 : List Nat := [0x20,0x80000000000000000000,0x200000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 320. -/
noncomputable def tree320 : ParitySearchTree := (.split 5 .done (.split 52 (.pack [7]) (.split 55 (.pack [6]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 68 (.pack [9]) (.split 79 .done (.split 83 (.pack [10]) (.split 93 .done (.split 106 .done (.split 107 (.pack [0]) (.split 122 (.pack [2]) (.split 156 (.pack [9]) (.split 158 (.pack [3]) (.split 169 (.pack [4]) (.split 170 (.pack [5]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 320. -/
theorem checked320 : checkParitySearch 8 (fun q => (rows320 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed320.contains) tree320 0xffefffffffffffdbeedfdbbfeffb3fff7fffffffd7ea7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 321. -/
noncomputable def rows321 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000002006000c000040008004008001600400090000000200000000000000000000006006c200040010004008404c00000410001001000340000000000000000000006000a00000000800c000400a01a0012000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 321. -/
noncomputable def allowed321 : List Nat := [0x4,0x80000000000000000000,0x40000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 321. -/
noncomputable def tree321 : ParitySearchTree := (.split 2 .done (.split 49 (.pack [4]) (.split 52 (.pack [8]) (.split 65 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 77 (.pack [10]) (.split 79 .done (.split 90 .done (.split 106 .done (.split 107 (.pack [2]) (.split 119 (.pack [1]) (.split 153 (.pack [7]) (.split 155 (.pack [3]) (.split 169 (.pack [5]) (.split 170 (.pack [6]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 321. -/
theorem checked321 : checkParitySearch 8 (fun q => (rows321 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed321.contains) tree321 0xffefffffffffffd9bfd7fd7fef7fe7ff7fffffffd1ffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 322. -/
noncomputable def rows322 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 322. -/
noncomputable def allowed322 : List Nat := [0x1000,0x2000,0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 322. -/
noncomputable def tree322 : ParitySearchTree := (.split 9 (.pack [0]) (.split 10 (.pack [1]) (.split 11 (.pack [2]) (.split 12 .done (.split 13 .done (.split 14 .done (.split 24 (.pack [4]) (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 141 (.pack [7]) (.split 142 (.pack [8]) (.split 143 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 322. -/
theorem checked322 : checkParitySearch 8 (fun q => (rows322 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed322.contains) tree322 0xffefffffffffffd43fa3fdbfec7fffff7fffffffd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 323. -/
noncomputable def rows323 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004c00c00c0480000028006008809100100900002402000000000000000000000000000000000200000030048000000000000000001000000000000000000000004006000c040048002004c08a00d0040009000020000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 323. -/
noncomputable def allowed323 : List Nat := [0x20000,0x80000000000000000000,0x40000000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 323. -/
noncomputable def tree323 : ParitySearchTree := (.split 17 .done (.split 36 (.pack [5]) (.split 39 (.pack [6]) (.split 54 (.pack [10]) (.split 64 (.pack [11]) (.split 66 (.pack [13]) (.split 67 (.pack [12]) (.split 77 (.pack [14]) (.split 79 .done (.split 83 (.pack [1]) (.split 90 .done (.split 91 (.pack [11]) (.split 94 (.pack [12]) (.split 105 .done (.split 119 (.pack [2]) (.split 122 (.pack [2]) (.split 134 (.pack [8]) (.split 142 (.pack [3]) (.split 143 (.pack [4]) (.split 157 (.pack [7]) (.split 158 (.pack [12]) (.split 170 (.pack [9]) (.zero 0)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 323. -/
theorem checked323 : checkParitySearch 8 (fun q => (rows323 >>> (256*q)) &&& (2^256-1)) 0x5 (allowed323.contains) tree323 0xffefffffffffffc9ff2bfcffebffd7ff7fffffffe7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 324. -/
noncomputable def rows324 : Nat := 0x300000000000000080000010012000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000100000050024000000000000000000800000000000000000000000000030002004000a00a004800000000001801a00020000000000000000000036000010012004004800c0000020800000008000008a

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 324. -/
noncomputable def allowed324 : List Nat := [0x20000,0x80000000000000000000,0x200000000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 324. -/
noncomputable def tree324 : ParitySearchTree := (.split 1 (.pack [3]) (.split 17 .done (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 79 .done (.split 82 (.pack [2]) (.split 93 .done (.split 95 (.pack [9]) (.split 105 .done (.split 107 (.pack [0]) (.split 122 (.pack [0]) (.split 133 (.pack [7]) (.split 148 (.pack [8]) (.split 149 (.pack [8]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 324. -/
theorem checked324 : checkParitySearch 8 (fun q => (rows324 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed324.contains) tree324 0xffefffffffffffc9fef7ff3febffafff7fffffffe7fca 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 325. -/
noncomputable def rows325 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000000004000001400100000000000000000020020000000000000000000000000030002004000a00a004800000000001801a000200000000000000000001b6000010092004024800c0100100800000008040040a0000000000000000000002000c00c00000800800080020128001009000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 325. -/
noncomputable def allowed325 : List Nat := [0x20000,0x80000000000000000000,0x200000000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 325. -/
noncomputable def tree325 : ParitySearchTree := (.split 1 (.pack [3]) (.split 17 .done (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 79 .done (.split 82 (.pack [10]) (.split 93 .done (.split 95 (.pack [9]) (.split 105 .done (.split 107 (.pack [0]) (.split 122 (.pack [1]) (.split 133 (.pack [7]) (.split 148 (.pack [8]) (.split 149 (.pack [8]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 325. -/
theorem checked325 : checkParitySearch 8 (fun q => (rows325 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed325.contains) tree325 0xffefffffffffffc9f7bfefbfebfdbfff7fffffffe7e4f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 326. -/
noncomputable def rows326 : Nat := (Nat.lor 0x400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000001000000c002400000000000000000080000000000000000000002000600c0080080090002001810701300900000400000000000000000000000006006000048004008000601481c30240000000240220000000000000000000002600000c00800200800060150103037009000004005 (Nat.shiftLeft 0xa0000000000000008000001001200000000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 326. -/
noncomputable def allowed326 : List Nat := [0x1,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 326. -/
noncomputable def tree326 : ParitySearchTree := (.split 0 .done (.split 2 .done (.split 14 (.pack [5]) (.split 36 (.pack [7]) (.split 39 (.pack [8]) (.split 48 (.pack [9]) (.split 49 (.pack [10]) (.split 50 (.pack [11]) (.split 52 (.pack [16]) (.split 53 (.pack [17]) (.split 60 (.pack [14]) (.split 61 (.pack [15]) (.split 68 (.pack [17]) (.split 76 (.pack [18]) (.split 78 (.pack [3]) (.split 80 (.pack [1]) (.split 89 (.pack [4]) (.split 90 (.pack [1]) (.split 107 (.pack [2]) (.split 117 (.pack [6]) (.split 131 (.pack [8]) (.split 142 (.pack [13]) (.split 143 (.pack [5]) (.split 165 (.pack [9]) (.split 166 (.pack [10]) (.split 169 (.pack [12]) (.zero 0)))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 326. -/
theorem checked326 : checkParitySearch 8 (fun q => (rows326 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed326.contains) tree326 0xffefffffffffffbeff93fc7ff5ffc7ff7fffffffe4fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 327. -/
noncomputable def rows327 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 327. -/
noncomputable def allowed327 : List Nat := [0x1000,0x2000,0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 327. -/
noncomputable def tree327 : ParitySearchTree := (.split 9 (.pack [0]) (.split 10 (.pack [1]) (.split 11 (.pack [2]) (.split 12 .done (.split 13 .done (.split 14 .done (.split 24 (.pack [4]) (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 141 (.pack [7]) (.split 142 (.pack [8]) (.split 143 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 327. -/
theorem checked327 : checkParitySearch 8 (fun q => (rows327 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed327.contains) tree327 0xffefffffffffffb83f63fdbff47fffff7fffffffe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 328. -/
noncomputable def rows328 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000180370030060000000000000000000c016018f000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000010032001006a006009000000000000801001820000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 328. -/
noncomputable def allowed328 : List Nat := [0x1,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 328. -/
noncomputable def tree328 : ParitySearchTree := (.split 0 .done (.split 1 (.pack [1]) (.split 2 .done (.split 3 (.pack [0]) (.split 7 (.pack [2]) (.split 8 (.pack [3]) (.split 17 (.pack [6]) (.split 18 (.pack [5]) (.split 20 (.pack [7]) (.split 30 (.pack [8]) (.split 31 (.pack [9]) (.split 109 (.pack [5]) (.split 110 (.pack [5]) (.split 120 (.pack [7]) (.split 121 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [8]) (.split 134 (.pack [8]) (.split 136 (.pack [10]) (.split 137 (.pack [10]) (.split 147 (.pack [11]) (.split 148 (.pack [12]) (.zero 4)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 328. -/
theorem checked328 : checkParitySearch 8 (fun q => (rows328 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed328.contains) tree328 0xffefffffffffffb7fea3fe7ff7ff87ff7fffffffe7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 329. -/
noncomputable def rows329 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000038005000000a000000000000000001c01d002d

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 329. -/
noncomputable def allowed329 : List Nat := [0x1,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 329. -/
noncomputable def tree329 : ParitySearchTree := (.split 0 .done (.split 2 .done (.split 3 (.pack [2]) (.split 5 (.pack [4]) (.split 16 (.pack [1]) (.split 18 (.pack [2]) (.split 19 (.pack [3]) (.split 20 (.pack [4]) (.split 30 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 105 (.pack [1]) (.split 107 (.pack [1]) (.split 132 (.pack [6]) (.split 134 (.pack [6]) (.split 147 (.pack [9]) (.split 148 (.pack [10]) (.split 149 (.pack [8]) (.zero 0)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 329. -/
theorem checked329 : checkParitySearch 8 (fun q => (rows329 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed329.contains) tree329 0xffefffffffffffa5ffa3fc7ff3ffc7ff7fffffffd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 330. -/
noncomputable def rows330 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000038005000000a000000000000000001c01d002d00000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 330. -/
noncomputable def allowed330 : List Nat := [0x8,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 330. -/
noncomputable def tree330 : ParitySearchTree := (.split 0 (.pack [0]) (.split 2 (.pack [1]) (.split 3 .done (.split 5 .done (.split 16 (.pack [3]) (.split 18 (.pack [4]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 30 (.pack [7]) (.split 31 (.pack [8]) (.split 32 (.pack [9]) (.split 105 (.pack [3]) (.split 107 (.pack [3]) (.split 132 (.pack [8]) (.split 134 (.pack [8]) (.split 147 (.pack [11]) (.split 148 (.pack [12]) (.split 149 (.pack [10]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 330. -/
theorem checked330 : checkParitySearch 8 (fun q => (rows330 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed330.contains) tree330 0xffefffffffffffa5f8bff3bff3fe3fff7fffffffd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 331. -/
noncomputable def rows331 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000002000001800080000000000000000010010000000000000000000006600a00000000800d000400801840120000000000040000000000000000000006a00600000000400c800401001820240000000000020000000000000000000006000c00000000200c000001c8180036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 331. -/
noncomputable def allowed331 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 331. -/
noncomputable def tree331 : ParitySearchTree := (.split 2 .done (.split 49 (.pack [9]) (.split 52 (.pack [12]) (.split 62 (.pack [14]) (.split 67 (.pack [12]) (.split 68 (.pack [13]) (.split 79 (.pack [0]) (.split 90 (.pack [1]) (.split 104 (.pack [3]) (.split 106 (.pack [4]) (.split 107 (.pack [4]) (.split 119 (.pack [5]) (.split 153 (.pack [6]) (.split 155 (.pack [7]) (.split 165 (.pack [8]) (.split 166 (.pack [9]) (.split 169 (.pack [10]) (.split 170 (.pack [11]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 331. -/
theorem checked331 : checkParitySearch 8 (fun q => (rows331 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed331.contains) tree331 0xffefffffffffff9e7fdbfc7ffcffc7ff7fffffffc9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 332. -/
noncomputable def rows332 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 332. -/
noncomputable def allowed332 : List Nat := [0x2000,0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 332. -/
noncomputable def tree332 : ParitySearchTree := (.split 9 (.pack [0]) (.split 10 (.pack [1]) (.split 11 (.pack [2]) (.split 12 (.pack [4]) (.split 13 .done (.split 14 .done (.split 24 (.pack [5]) (.split 25 (.pack [6]) (.split 26 (.pack [7]) (.split 141 (.pack [8]) (.split 142 (.pack [9]) (.split 143 (.pack [8]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 332. -/
theorem checked332 : checkParitySearch 8 (fun q => (rows332 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed332.contains) tree332 0xffefffffffffff9c3f23fdbffc7fffff7fffffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 333. -/
noncomputable def rows333 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c000000000000000000000080090000000000000000000004600c00c008000004000600980830010090000040040000000000000000000602a00c0080040004080007010c1050010090020004020000000000000000000006600a00000000800d000400801840120000000000040000000000000000000006000c00000000200c000001c8180036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 333. -/
noncomputable def allowed333 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 333. -/
noncomputable def tree333 : ParitySearchTree := (.split 2 .done (.split 49 (.pack [8]) (.split 52 (.pack [11]) (.split 62 (.pack [13]) (.split 67 (.pack [11]) (.split 68 (.pack [12]) (.split 79 (.pack [0]) (.split 90 (.pack [2]) (.split 104 (.pack [3]) (.split 106 (.pack [4]) (.split 107 (.pack [4]) (.split 119 (.pack [3]) (.split 153 (.pack [5]) (.split 155 (.pack [6]) (.split 165 (.pack [7]) (.split 166 (.pack [8]) (.split 169 (.pack [9]) (.split 170 (.pack [10]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 333. -/
theorem checked333 : checkParitySearch 8 (fun q => (rows333 >>> (256*q)) &&& (2^256-1)) 0xa (allowed333.contains) tree333 0xffefffffffffff9affd3fc7ffdffc7ff7fffffffccfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 334. -/
noncomputable def rows334 : Nat := (Nat.lor 0x500000000000000040000008009000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c000000000000000000000080090000000000000000000a04600c0040080004040007008a0830010090040008040000000000000000000002a00c00c00400000800050128105001009000002002000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000006000c00000000200c000001c8180036000000000001 (Nat.shiftLeft 0xc000000000000000400000080090000000000000000000000000000000000000000140000000000000010000002002400000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 334. -/
noncomputable def allowed334 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 334. -/
noncomputable def tree334 : ParitySearchTree := (.split 2 .done (.split 11 (.pack [2]) (.split 26 (.pack [9]) (.split 36 (.pack [7]) (.split 39 (.pack [10]) (.split 48 (.pack [11]) (.split 60 (.pack [14]) (.split 61 (.pack [16]) (.split 67 (.pack [15]) (.split 73 (.pack [16]) (.split 75 (.pack [17]) (.split 79 (.pack [0]) (.split 88 (.pack [1]) (.split 89 (.pack [2]) (.split 90 (.pack [3]) (.split 106 (.pack [5]) (.split 114 (.pack [17]) (.split 131 (.pack [10]) (.split 142 (.pack [6]) (.split 154 (.pack [8]) (.split 155 (.pack [9]) (.split 165 (.pack [11]) (.split 166 (.pack [12]) (.split 170 (.pack [13]) (.split 177 (.pack [14]) (.split 179 (.pack [17]) (.zero 4)))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 334. -/
theorem checked334 : checkParitySearch 8 (fun q => (rows334 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed334.contains) tree334 0xffefffffffffff977fcbfc7ffeffc7ff7fffffffcafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 335. -/
noncomputable def rows335 : Nat := (Nat.lor 0x600000000000000100000020024000000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400000000000000000000020024000000000000000000000a02a00c044040006400800500c20c20010090240008240000000000000000000a04600c0040080004040007008a083001009004000804000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000006000a000010002000001001c81a0012000000008008 (Nat.shiftLeft 0xc00000000000000040000008009000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 335. -/
noncomputable def allowed335 : List Nat := [0x4,0x40000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 335. -/
noncomputable def tree335 : ParitySearchTree := (.split 2 .done (.split 11 (.pack [2]) (.split 26 (.pack [8]) (.split 36 (.pack [6]) (.split 39 (.pack [9]) (.split 48 (.pack [10]) (.split 60 (.pack [12]) (.split 61 (.pack [14]) (.split 67 (.pack [13]) (.split 73 (.pack [14]) (.split 75 (.pack [16]) (.split 79 (.pack [0]) (.split 88 (.pack [1]) (.split 89 (.pack [2]) (.split 90 .done (.split 106 (.pack [4]) (.split 114 (.pack [16]) (.split 131 (.pack [9]) (.split 142 (.pack [5]) (.split 154 (.pack [7]) (.split 155 (.pack [8]) (.split 165 (.pack [10]) (.split 166 (.pack [15]) (.split 170 (.pack [11]) (.split 177 (.pack [12]) (.split 179 (.pack [16]) (.zero 3)))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 335. -/
theorem checked335 : checkParitySearch 8 (fun q => (rows335 >>> (256*q)) &&& (2^256-1)) 0x18 (allowed335.contains) tree335 0xffefffffffffff977f5bfd7ffeffe7ff7fffffffcaffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 336. -/
noncomputable def rows336 : Nat := 0x6006c00000000000200240040000041000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000038036000006c000000000000000001c00481860000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000280040010006006009000000000001401480040000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 336. -/
noncomputable def allowed336 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 336. -/
noncomputable def tree336 : ParitySearchTree := (.split 2 .done (.split 15 (.pack [3]) (.split 18 (.pack [5]) (.split 20 (.pack [6]) (.split 30 (.pack [7]) (.split 32 (.pack [8]) (.split 80 (.pack [4]) (.split 83 (.pack [2]) (.split 93 (.pack [10]) (.split 94 (.pack [0]) (.split 105 (.pack [10]) (.split 106 (.pack [3]) (.split 120 (.pack [0]) (.split 134 (.pack [7]) (.split 147 (.pack [9]) (.split 149 (.pack [9]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 336. -/
theorem checked336 : checkParitySearch 8 (fun q => (rows336 >>> (256*q)) &&& (2^256-1)) 0x12 (allowed336.contains) tree336 0xffefffffffffff93fee3fe7fffff87ff7fffffffcffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 337. -/
noncomputable def rows337 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f80000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 337. -/
noncomputable def allowed337 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 337. -/
noncomputable def tree337 : ParitySearchTree := (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 18 (.pack [0]) (.split 19 (.pack [1]) (.split 20 (.pack [2]) (.split 30 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 147 (.pack [9]) (.split 148 (.pack [10]) (.split 149 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 337. -/
theorem checked337 : checkParitySearch 8 (fun q => (rows337 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed337.contains) tree337 0xffefffffffffff8c7f07fdbff8ffffff7ffffffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 338. -/
noncomputable def rows338 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f80000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000060000000010000000000001801b0000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 338. -/
noncomputable def allowed338 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 338. -/
noncomputable def tree338 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 (.pack [4]) (.split 17 .done (.split 18 (.pack [1]) (.split 19 (.pack [2]) (.split 20 (.pack [3]) (.split 30 (.pack [6]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 147 (.pack [10]) (.split 148 (.pack [11]) (.split 149 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 338. -/
theorem checked338 : checkParitySearch 8 (fun q => (rows338 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed338.contains) tree338 0xffefffffffffff8abf0bfdbff97fffff7ffffffffafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 339. -/
noncomputable def rows339 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f80000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000030000000000000c00d800000000001801b0030

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 339. -/
noncomputable def allowed339 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 339. -/
noncomputable def tree339 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 (.pack [1]) (.split 17 .done (.split 18 (.pack [2]) (.split 19 (.pack [3]) (.split 20 (.pack [4]) (.split 30 (.pack [6]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 147 (.pack [10]) (.split 148 (.pack [11]) (.split 149 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 339. -/
theorem checked339 : checkParitySearch 8 (fun q => (rows339 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed339.contains) tree339 0xffefffffffffff88ffbbfcfff9ffd7ff7ffffffffcffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 340. -/
noncomputable def rows340 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f8000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000060000000010000000000001801b0000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 340. -/
noncomputable def allowed340 : List Nat := [0x10000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 340. -/
noncomputable def tree340 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 .done (.split 17 (.pack [4]) (.split 18 (.pack [1]) (.split 19 (.pack [2]) (.split 20 (.pack [3]) (.split 30 (.pack [6]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 147 (.pack [10]) (.split 148 (.pack [11]) (.split 149 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 340. -/
theorem checked340 : checkParitySearch 8 (fun q => (rows340 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed340.contains) tree340 0xffefffffffffff873f13fdbffa7fffff7ffffffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 341. -/
noncomputable def rows341 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f80000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000030000000000000c00d800000000001801b0030

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 341. -/
noncomputable def allowed341 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 341. -/
noncomputable def tree341 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 (.pack [1]) (.split 17 .done (.split 18 (.pack [2]) (.split 19 (.pack [3]) (.split 20 (.pack [4]) (.split 30 (.pack [6]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 147 (.pack [10]) (.split 148 (.pack [11]) (.split 149 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 341. -/
theorem checked341 : checkParitySearch 8 (fun q => (rows341 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed341.contains) tree341 0xffefffffffffff83bfaffcfffb7fd7ff7ffffffff9ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 342. -/
noncomputable def rows342 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c002000000000000000000400400000000000000000000066000000012000000800081a01940000000000090080000000000000000000036000010020000002200a00900208000000080190108

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 342. -/
noncomputable def allowed342 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 342. -/
noncomputable def tree342 : ParitySearchTree := (.split 12 (.pack [3]) (.split 13 (.pack [4]) (.split 14 (.pack [2]) (.split 15 (.pack [1]) (.split 16 (.pack [0]) (.split 17 .done (.split 27 (.pack [6]) (.split 28 (.pack [7]) (.split 29 (.pack [8]) (.split 144 (.pack [10]) (.split 145 (.pack [11]) (.split 146 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 342. -/
theorem checked342 : checkParitySearch 8 (fun q => (rows342 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed342.contains) tree342 0xffefffffffffff81feaffebffbff9fff7ffffffffffcc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 343. -/
noncomputable def rows343 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400100000000000000000020020000000000000000000006a000000012000001000081901a20000000000090080000000000000000000036000010020000002200a00900208000000080190108

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 343. -/
noncomputable def allowed343 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 343. -/
noncomputable def tree343 : ParitySearchTree := (.split 12 (.pack [3]) (.split 13 (.pack [2]) (.split 14 (.pack [4]) (.split 15 (.pack [1]) (.split 16 (.pack [0]) (.split 17 .done (.split 27 (.pack [6]) (.split 28 (.pack [7]) (.split 29 (.pack [8]) (.split 144 (.pack [10]) (.split 145 (.pack [11]) (.split 146 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 343. -/
theorem checked343 : checkParitySearch 8 (fun q => (rows343 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed343.contains) tree343 0xffefffffffffff81fe77ff3ffbffafff7ffffffffffca 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 344. -/
noncomputable def rows344 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 344. -/
noncomputable def allowed344 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 344. -/
noncomputable def tree344 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 344. -/
theorem checked344 : checkParitySearch 8 (fun q => (rows344 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed344.contains) tree344 0xffefffffffffff81f9dff1bffbfe7fff7ffffffffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 345. -/
noncomputable def rows345 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000006006c02000000000200300128000041000010012005

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 345. -/
noncomputable def allowed345 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 345. -/
noncomputable def tree345 : ParitySearchTree := (.split 12 (.pack [1]) (.split 13 (.pack [2]) (.split 14 (.pack [3]) (.split 15 (.pack [4]) (.split 16 (.pack [0]) (.split 17 .done (.split 27 (.pack [6]) (.split 28 (.pack [7]) (.split 29 (.pack [8]) (.split 144 (.pack [10]) (.split 145 (.pack [11]) (.split 146 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 345. -/
theorem checked345 : checkParitySearch 8 (fun q => (rows345 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed345.contains) tree345 0xffefffffffffff81f73fefbffbfdbfff7fffffffffe4f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 346. -/
noncomputable def rows346 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 346. -/
noncomputable def allowed346 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 346. -/
noncomputable def tree346 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 346. -/
theorem checked346 : checkParitySearch 8 (fun q => (rows346 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed346.contains) tree346 0xffefffffffffff81f61fedbffbfdffff7fffffffffe7f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 347. -/
noncomputable def rows347 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 347. -/
noncomputable def allowed347 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 347. -/
noncomputable def tree347 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 347. -/
theorem checked347 : checkParitySearch 8 (fun q => (rows347 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed347.contains) tree347 0xffefffffffffff81ed1fddbffbfbffff7fffffffffebf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 348. -/
noncomputable def rows348 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 348. -/
noncomputable def allowed348 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 348. -/
noncomputable def tree348 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 348. -/
theorem checked348 : checkParitySearch 8 (fun q => (rows348 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed348.contains) tree348 0xffefffffffffff81db1fbdbffbf7ffff7ffffffffff3f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 349. -/
noncomputable def rows349 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 349. -/
noncomputable def allowed349 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 349. -/
noncomputable def tree349 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 349. -/
theorem checked349 : checkParitySearch 8 (fun q => (rows349 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed349.contains) tree349 0xffefffffffffff81b71f7dbffbefffff7fffffffff3ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 350. -/
noncomputable def rows350 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 350. -/
noncomputable def allowed350 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 350. -/
noncomputable def tree350 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 350. -/
theorem checked350 : checkParitySearch 8 (fun q => (rows350 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed350.contains) tree350 0xffefffffffffff816f1efdbffbdfffff7fffffffff5ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 351. -/
noncomputable def rows351 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 351. -/
noncomputable def allowed351 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 351. -/
noncomputable def tree351 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 351. -/
theorem checked351 : checkParitySearch 8 (fun q => (rows351 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed351.contains) tree351 0xffefffffffffff80df1dfdbffbbfffff7fffffffff9ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 352. -/
noncomputable def rows352 : Nat := 0x1400000000000000100000020024000000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000008000002800000000000000000000040048000000000000000000000001000200280030060000000000000008008000a01b000000000000000000000000000000000200000030000000000000000000001001200000000000000000000002006000c00004000800400800160040009000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 352. -/
noncomputable def allowed352 : List Nat := [0x10000,0x20000,0x2000000000000000000000000000000,0x2000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 352. -/
noncomputable def tree352 : ParitySearchTree := (.split 16 .done (.split 17 .done (.split 19 (.pack [3]) (.split 20 (.pack [1]) (.split 29 (.pack [4]) (.split 31 (.pack [5]) (.split 47 (.pack [7]) (.split 59 (.pack [9]) (.split 121 .done (.split 122 (.pack [0]) (.split 132 (.pack [5]) (.split 133 .done (.split 147 (.pack [6]) (.split 149 (.pack [6]) (.split 161 (.pack [8]) (.split 176 (.pack [10]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 352. -/
theorem checked352 : checkParitySearch 8 (fun q => (rows352 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed352.contains) tree352 0xffeffffedfefffe9ff9ffdbfebffffff7ebfebfff7fef 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 353. -/
noncomputable def rows353 : Nat := 0x1400000000000000100000020024000000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000001000200280030060000000000000008008000a01b00000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000002000000a004800000000000000000100000000000000000000036100020008002004200c000002080008008001a0098

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 353. -/
noncomputable def allowed353 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 353. -/
noncomputable def tree353 : ParitySearchTree := (.split 16 (.pack [2]) (.split 17 .done (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 29 (.pack [6]) (.split 31 (.pack [7]) (.split 47 (.pack [9]) (.split 59 (.pack [11]) (.split 121 (.pack [1]) (.split 122 (.pack [0]) (.split 132 (.pack [7]) (.split 133 (.pack [2]) (.split 147 (.pack [8]) (.split 149 (.pack [8]) (.split 161 (.pack [10]) (.split 176 (.pack [12]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 353. -/
theorem checked353 : checkParitySearch 8 (fun q => (rows353 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed353.contains) tree353 0xffeffffedfefffe9febfffbfebffbfff7ebfebfff7fdf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 354. -/
noncomputable def rows354 : Nat := 0xc000000000000002000000400480000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000008009006006c000000000000000000400000410000000000000000000000000080010012005000a000000000000004004001401ea00000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 354. -/
noncomputable def allowed354 : List Nat := [0x20000,0x800000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 354. -/
noncomputable def tree354 : ParitySearchTree := (.split 13 (.pack [1]) (.split 15 (.pack [2]) (.split 17 .done (.split 18 (.pack [3]) (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 30 (.pack [9]) (.split 32 (.pack [8]) (.split 46 (.pack [10]) (.split 58 (.pack [13]) (.split 117 (.pack [0]) (.split 119 .done (.split 132 (.pack [8]) (.split 134 (.pack [7]) (.split 145 (.pack [11]) (.split 148 (.pack [12]) (.split 160 (.pack [14]) (.split 175 (.pack [15]) (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 354. -/
theorem checked354 : checkParitySearch 8 (fun q => (rows354 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed354.contains) tree354 0xffeffffdf7ffff9bff3ffdbfffffffff7f27fe7febffb 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 355. -/
noncomputable def rows355 : Nat := 0xc00000000000000040000008009000000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000002006000c040000000002000c009804000900002002400000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 355. -/
noncomputable def allowed355 : List Nat := [0x20000,0x4000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 355. -/
noncomputable def tree355 : ParitySearchTree := (.split 2 (.pack [2]) (.split 5 (.pack [1]) (.split 17 .done (.split 36 (.pack [7]) (.split 39 (.pack [8]) (.split 54 (.pack [13]) (.split 63 (.pack [14]) (.split 64 (.pack [11]) (.split 67 (.pack [12]) (.split 78 (.pack [0]) (.split 79 (.pack [3]) (.split 93 (.pack [1]) (.split 134 .done (.split 142 (.pack [5]) (.split 143 (.pack [6]) (.split 157 (.pack [9]) (.split 158 (.pack [12]) (.split 169 (.pack [10]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 355. -/
theorem checked355 : checkParitySearch 8 (fun q => (rows355 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed355.contains) tree355 0xffeffffdbfdfffd3fe1fffbfffffbfff7f3ff3ffeffef 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 356. -/
noncomputable def rows356 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000004000000600000000000000000000020024000000000000000000002e00000000900000400000058053000000000004804100000000000000000000000000000000200000030048000000000000000001000000000000000000000004003000c000040004000009800500d0009000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 356. -/
noncomputable def allowed356 : List Nat := [0x4000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 356. -/
noncomputable def tree356 : ParitySearchTree := (.split 5 (.pack [3]) (.split 36 (.pack [5]) (.split 39 (.pack [6]) (.split 52 (.pack [9]) (.split 54 (.pack [11]) (.split 55 (.pack [12]) (.split 64 (.pack [9]) (.split 66 (.pack [13]) (.split 79 (.pack [2]) (.split 80 (.pack [2]) (.split 83 (.pack [1]) (.split 106 (.pack [3]) (.split 122 .done (.split 142 (.pack [4]) (.split 143 (.pack [7]) (.split 156 (.pack [6]) (.split 157 (.pack [10]) (.split 170 (.pack [8]) (.zero 0)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 356. -/
theorem checked356 : checkParitySearch 8 (fun q => (rows356 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed356.contains) tree356 0xffeffffdbfdfffd3fd7ff9bfffff7fff7f3ff3ffefff7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 357. -/
noncomputable def rows357 : Nat := 0xc00000000000000040000008009000000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000002006000c040000000002000c009804000900002002400000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 357. -/
noncomputable def allowed357 : List Nat := [0x20,0x20000,0x80000000000000000000,0x200000000000000000000000,0x4000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 357. -/
noncomputable def tree357 : ParitySearchTree := (.split 2 (.pack [1]) (.split 5 .done (.split 17 .done (.split 36 (.pack [5]) (.split 39 (.pack [6]) (.split 54 (.pack [11]) (.split 63 (.pack [12]) (.split 64 (.pack [9]) (.split 67 (.pack [10]) (.split 78 (.pack [0]) (.split 79 .done (.split 93 .done (.split 134 .done (.split 142 (.pack [3]) (.split 143 (.pack [4]) (.split 157 (.pack [7]) (.split 158 (.pack [10]) (.split 169 (.pack [8]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 357. -/
theorem checked357 : checkParitySearch 8 (fun q => (rows357 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed357.contains) tree357 0xffeffffdbfdfff9bfe9fffbfefffbfff7f3ff3fff7fef 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 358. -/
noncomputable def rows358 : Nat := 0xc000000000000002000000400480000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000001000000180000000000000000000008009000000000000000000000000140020008003003000000000000000a00a40020120000000000000000000000000000000800000600000000000000000000004004800000000000000000000000060000000010000000000001801b00000000000080090000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 358. -/
noncomputable def allowed358 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 358. -/
noncomputable def tree358 : ParitySearchTree := (.split 17 .done (.split 20 (.pack [4]) (.split 29 (.pack [5]) (.split 42 (.pack [6]) (.split 45 (.pack [7]) (.split 47 (.pack [8]) (.split 57 (.pack [9]) (.split 59 (.pack [10]) (.split 120 (.pack [0]) (.split 121 (.pack [2]) (.split 132 (.pack [1]) (.split 133 (.pack [6]) (.split 147 (.pack [2]) (.split 161 (.pack [9]) (.split 174 (.pack [12]) (.split 176 (.pack [11]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 358. -/
theorem checked358 : checkParitySearch 8 (fun q => (rows358 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed358.contains) tree358 0xffeffffc9fcffff3ff3ffdbfffffffff7e7fe7fffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 359. -/
noncomputable def rows359 : Nat := 0xc000000000000002000000400480000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000001000000180000000000000000000008009000000000000000000000000140020008003003000000000000000a00a40020120000000000000000000000000000000800000600000000000000000000004004800000000000000000000000060000000010000000000001801b00000000000080090000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 359. -/
noncomputable def allowed359 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 359. -/
noncomputable def tree359 : ParitySearchTree := (.split 17 .done (.split 20 (.pack [5]) (.split 29 (.pack [6]) (.split 42 (.pack [7]) (.split 45 (.pack [8]) (.split 47 (.pack [9]) (.split 57 (.pack [10]) (.split 59 (.pack [11]) (.split 120 (.pack [0]) (.split 121 (.pack [1]) (.split 132 (.pack [2]) (.split 133 (.pack [7]) (.split 147 (.pack [3]) (.split 161 (.pack [10]) (.split 174 (.pack [13]) (.split 176 (.pack [12]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 359. -/
theorem checked359 : checkParitySearch 8 (fun q => (rows359 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed359.contains) tree359 0xffeffffc9fcffff3fe1fffbfffffbfff7e7fe7fffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 360. -/
noncomputable def rows360 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 360. -/
noncomputable def allowed360 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 360. -/
noncomputable def tree360 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 360. -/
theorem checked360 : checkParitySearch 8 (fun q => (rows360 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed360.contains) tree360 0xffeffff6ffefff81ff1ffdbffbffffff75ffffff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 361. -/
noncomputable def rows361 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 361. -/
noncomputable def allowed361 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 361. -/
noncomputable def tree361 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 361. -/
theorem checked361 : checkParitySearch 8 (fun q => (rows361 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed361.contains) tree361 0xffefffedffdfff81ff1ffdbffbffffff79fffffefffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 362. -/
noncomputable def rows362 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200c00d8000000000004004000800000820000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000002000400c0018000080010010010002c0080012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000002200c00d840000000000400c00d000000820002002400000000000000000000000000000000040000006009000000000000000000200000000000000000000000600c00000000800100140100014036000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 362. -/
noncomputable def allowed362 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 362. -/
noncomputable def tree362 : ParitySearchTree := (.split 2 .done (.split 49 (.pack [7]) (.split 50 (.pack [8]) (.split 52 (.pack [11]) (.split 53 (.pack [12]) (.split 62 (.pack [10]) (.split 64 (.pack [13]) (.split 80 (.pack [1]) (.split 90 (.pack [9]) (.split 92 (.pack [4]) (.split 104 (.pack [2]) (.split 119 (.pack [3]) (.split 154 (.pack [5]) (.split 155 (.pack [6]) (.split 165 (.pack [13]) (.split 166 (.pack [7]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 362. -/
theorem checked362 : checkParitySearch 8 (fun q => (rows362 >>> (256*q)) &&& (2^256-1)) 0x5 (allowed362.contains) tree362 0xffefffdffffffffb7f9f7f4ffdffd6ffeffefffffaffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 363. -/
noncomputable def rows363 : Nat := 0xc0000000000000004000000800900000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000200c00d800000000000400400080000082000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000800000280000000000000000000004004800000000000000000000a000000008009800400f000601200000000000400040400000000000000000000000000000000400000300090000000000000000002000000000000000000000000000000000020000003004800000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 363. -/
noncomputable def allowed363 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 363. -/
noncomputable def tree363 : ParitySearchTree := (.split 2 .done (.split 10 (.pack [3]) (.split 26 (.pack [6]) (.split 73 (.pack [10]) (.split 76 (.pack [11]) (.split 85 (.pack [12]) (.split 86 (.pack [0]) (.split 100 (.pack [10]) (.split 101 (.pack [1]) (.split 102 (.pack [9]) (.split 103 (.pack [11]) (.split 114 (.pack [4]) (.split 127 (.pack [6]) (.split 128 (.pack [5]) (.split 131 (.pack [7]) (.split 143 (.pack [8]) (.split 177 (.pack [9]) (.split 179 (.pack [13]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 363. -/
theorem checked363 : checkParitySearch 8 (fun q => (rows363 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed363.contains) tree363 0xffefffdffffffffb7f0f7e4ffdfff6ffeffefffffafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 364. -/
noncomputable def rows364 : Nat := 0x14000000000000001000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a000000000000000000000100120000000000000000000a00000000c00400100140000012000000000006004c020000000000000000000600d8000080008000006000a012008200000004004c00

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 364. -/
noncomputable def allowed364 : List Nat := [0x4000,0x10000000000000000000,0x40000000000000000000000000,0x200000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 364. -/
noncomputable def tree364 : ParitySearchTree := (.split 1 (.pack [2]) (.split 10 (.pack [3]) (.split 11 (.pack [4]) (.split 14 .done (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 73 (.pack [11]) (.split 76 .done (.split 102 .done (.split 104 (.pack [0]) (.split 116 (.pack [0]) (.split 130 (.pack [7]) (.split 142 (.pack [9]) (.split 143 (.pack [8]) (.split 177 .done (.split 179 (.pack [10]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 364. -/
theorem checked364 : checkParitySearch 8 (fun q => (rows364 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed364.contains) tree364 0xffefffdffffffff93ff77f8ffd7fceffeffefffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 365. -/
noncomputable def rows365 : Nat := (Nat.lor 0x40000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000002200c00d840000000000400c00d000000820002002400000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c002400000000000000000080000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0x600000000000000100000020024000000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000200c00d80000000000040040008000008200000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 365. -/
noncomputable def allowed365 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 365. -/
noncomputable def tree365 : ParitySearchTree := (.split 2 .done (.split 5 (.pack [3]) (.split 17 (.pack [8]) (.split 33 (.pack [9]) (.split 39 (.pack [12]) (.split 64 (.pack [0]) (.split 66 (.pack [17]) (.split 67 (.pack [18]) (.split 78 (.pack [1]) (.split 79 (.pack [2]) (.split 90 (.pack [16]) (.split 134 (.pack [13]) (.split 139 (.pack [5]) (.split 140 (.pack [6]) (.split 142 (.pack [15]) (.split 143 (.pack [7]) (.split 154 (.pack [10]) (.split 155 (.pack [11]) (.split 165 (.pack [19]) (.split 169 (.pack [14]) (.zero 4)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 365. -/
theorem checked365 : checkParitySearch 8 (fun q => (rows365 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed365.contains) tree365 0xffefffdffffffff6ff177e4ffefff6ffeffefffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 366. -/
noncomputable def rows366 : Nat := (Nat.lor 0x60000000000000002000000400480000000000000000000000000000000200c00d8000000000004004000800000820000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000002200c00d840000000000400c00d000000820002002400000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c00240000000000000000008 (Nat.shiftLeft 0xa000000000000000800000100120000000000000000000000000000000000000005000000000000000400000080090000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 366. -/
noncomputable def allowed366 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 366. -/
noncomputable def tree366 : ParitySearchTree := (.split 2 .done (.split 5 (.pack [2]) (.split 17 (.pack [6]) (.split 33 (.pack [7]) (.split 39 (.pack [10]) (.split 64 (.pack [17]) (.split 66 (.pack [15]) (.split 67 (.pack [16]) (.split 78 (.pack [0]) (.split 79 (.pack [1]) (.split 90 (.pack [14]) (.split 134 (.pack [11]) (.split 139 (.pack [4]) (.split 140 (.pack [5]) (.split 142 (.pack [13]) (.split 143 (.pack [12]) (.split 154 (.pack [8]) (.split 155 (.pack [9]) (.split 165 (.pack [17]) (.split 169 (.pack [12]) (.zero 3)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 366. -/
theorem checked366 : checkParitySearch 8 (fun q => (rows366 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed366.contains) tree366 0xffefffdffffffff27f1f7e4ffffff6ffeffefffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 367. -/
noncomputable def rows367 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000a00d8000040010000005000c024008200000002002c00000000000000000000000000000000004000003000900000000000000000020000000000000000000000000000060000000000001801b0000000000030036006

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 367. -/
noncomputable def allowed367 : List Nat := [0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 367. -/
noncomputable def tree367 : ParitySearchTree := (.split 9 (.pack [1]) (.split 10 (.pack [3]) (.split 11 (.pack [4]) (.split 12 (.pack [0]) (.split 13 (.pack [2]) (.split 14 .done (.split 24 (.pack [8]) (.split 25 (.pack [6]) (.split 26 (.pack [7]) (.split 141 (.pack [9]) (.split 142 (.pack [10]) (.split 143 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 367. -/
theorem checked367 : checkParitySearch 8 (fun q => (rows367 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed367.contains) tree367 0xffefffdffffffff03fe77f8fff7fceffeffefffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 368. -/
noncomputable def rows368 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 368. -/
noncomputable def allowed368 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 368. -/
noncomputable def tree368 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 368. -/
theorem checked368 : checkParitySearch 8 (fun q => (rows368 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed368.contains) tree368 0xffefffb7ff7fff81ff1ffdbffbffffff2ffffffbfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 369. -/
noncomputable def rows369 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 369. -/
noncomputable def allowed369 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 369. -/
noncomputable def tree369 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 369. -/
theorem checked369 : checkParitySearch 8 (fun q => (rows369 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed369.contains) tree369 0xffefff6ffeffff81ff1ffdbffbffffff4ffffff7fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 370. -/
noncomputable def rows370 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000002002000c00c00000800800100020128001009000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000360000000120000048000002402080000000000900820000000000000000000018006000000004004000a001008801b0000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 370. -/
noncomputable def allowed370 : List Nat := [0x20,0x80000000000000000,0x200000000000000000000000,0x8000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 370. -/
noncomputable def tree370 : ParitySearchTree := (.split 5 .done (.split 52 (.pack [6]) (.split 53 (.pack [8]) (.split 55 (.pack [9]) (.split 56 (.pack [10]) (.split 67 .done (.split 71 (.pack [10]) (.split 80 (.pack [3]) (.split 93 .done (.split 95 (.pack [3]) (.split 110 (.pack [1]) (.split 122 (.pack [2]) (.split 157 (.pack [4]) (.split 158 (.pack [5]) (.split 171 .done (.split 172 (.pack [7]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 370. -/
theorem checked370 : checkParitySearch 8 (fun q => (rows370 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed370.contains) tree370 0xffeffefffffffffffcd7eb7f3ffeaffbfff7fffffffe2 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 371. -/
noncomputable def rows371 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000002002000c00c00000800800100020128001009000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000180360000200100000042022004802080000001001a00000000000000000000018006000000004004000a001008801b0000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 371. -/
noncomputable def allowed371 : List Nat := [0x20,0x80000000000000000,0x200000000000000000000000,0x8000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 371. -/
noncomputable def tree371 : ParitySearchTree := (.split 5 .done (.split 52 (.pack [7]) (.split 53 (.pack [8]) (.split 55 (.pack [9]) (.split 56 (.pack [10]) (.split 67 .done (.split 71 (.pack [10]) (.split 80 (.pack [3]) (.split 93 .done (.split 95 (.pack [3]) (.split 110 (.pack [1]) (.split 122 (.pack [2]) (.split 157 (.pack [4]) (.split 158 (.pack [5]) (.split 171 .done (.split 172 (.pack [6]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 371. -/
theorem checked371 : checkParitySearch 8 (fun q => (rows371 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed371.contains) tree371 0xffeffefffffffffffcbbebbf3ffeb7fbfff7fffffffe1 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 372. -/
noncomputable def rows372 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000380000000000000000000000000001c01f80000000000000000000028036000010020000002204200900208000000080190000000000000000000000000000000000800000600120000000000000000004000000000000000000000000060000000010000000002401801b0000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 372. -/
noncomputable def allowed372 : List Nat := [0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 372. -/
noncomputable def tree372 : ParitySearchTree := (.split 3 (.pack [0]) (.split 4 (.pack [2]) (.split 5 .done (.split 6 (.pack [1]) (.split 7 (.pack [4]) (.split 8 (.pack [5]) (.split 18 (.pack [6]) (.split 19 (.pack [7]) (.split 20 (.pack [8]) (.split 135 (.pack [10]) (.split 136 (.pack [11]) (.split 137 (.pack [9]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 372. -/
theorem checked372 : checkParitySearch 8 (fun q => (rows372 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed372.contains) tree372 0xffeffefffffffffff88fe2ff3fff9ffbfff7ffffffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 373. -/
noncomputable def rows373 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000380000000000000000000000000001c01f8000000000000000000000c006006c02000000000200140128000041000010012000000000000000000000000000000000800000600120000000000000000004000000000000000000000000060000000010000000002401801b0000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 373. -/
noncomputable def allowed373 : List Nat := [0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 373. -/
noncomputable def tree373 : ParitySearchTree := (.split 3 (.pack [0]) (.split 4 (.pack [2]) (.split 5 .done (.split 6 (.pack [1]) (.split 7 (.pack [4]) (.split 8 (.pack [5]) (.split 18 (.pack [6]) (.split 19 (.pack [7]) (.split 20 (.pack [8]) (.split 135 (.pack [10]) (.split 136 (.pack [11]) (.split 137 (.pack [9]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 373. -/
theorem checked373 : checkParitySearch 8 (fun q => (rows373 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed373.contains) tree373 0xffeffefffffffffff857e37f3fffaffbfff7ffffffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 374. -/
noncomputable def rows374 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000380000000000000000000000000001c01f80000000000000000000028036000010020000002204200900208000000080190000000000000000000000000000000000800000600120000000000000000004000000000000000000000000060000000010000000002401801b0000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 374. -/
noncomputable def allowed374 : List Nat := [0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 374. -/
noncomputable def tree374 : ParitySearchTree := (.split 3 (.pack [0]) (.split 4 (.pack [2]) (.split 5 .done (.split 6 (.pack [1]) (.split 7 (.pack [4]) (.split 8 (.pack [5]) (.split 18 (.pack [6]) (.split 19 (.pack [7]) (.split 20 (.pack [8]) (.split 135 (.pack [10]) (.split 136 (.pack [11]) (.split 137 (.pack [9]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 374. -/
theorem checked374 : checkParitySearch 8 (fun q => (rows374 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed374.contains) tree374 0xffeffefffffffffff83be3bf3fffb7fbfff7ffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 375. -/
noncomputable def rows375 : Nat := 0x2000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 375. -/
noncomputable def allowed375 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 375. -/
noncomputable def tree375 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [7]) (.split 28 (.pack [5]) (.split 29 (.pack [6]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 375. -/
theorem checked375 : checkParitySearch 8 (fun q => (rows375 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed375.contains) tree375 0xffeffedffdffff81ff1ffdbffbfffffc7fffffeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 376. -/
noncomputable def rows376 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000006002000800a0014000000000000003002601000240000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 376. -/
noncomputable def allowed376 : List Nat := [0x10000000000000,0x20000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 376. -/
noncomputable def tree376 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [4]) (.split 49 (.pack [5]) (.split 50 (.pack [6]) (.split 51 (.pack [2]) (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 (.pack [2]) (.split 92 (.pack [2]) (.split 119 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 376. -/
theorem checked376 : checkParitySearch 8 (fun q => (rows376 >>> (256*q)) &&& (2^256-1)) 0x5 (allowed376.contains) tree376 0xffeffe9ff9ffffffffffdd3f53febff7ffefffcffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 377. -/
noncomputable def rows377 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000022006003000000000400c0008011008811f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000060040004006000c00000000000000300160200048000000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000000040000008009003803f000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 377. -/
noncomputable def allowed377 : List Nat := [0x8000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 377. -/
noncomputable def tree377 : ParitySearchTree := (.split 1 (.pack [1]) (.split 48 (.pack [4]) (.split 49 (.pack [5]) (.split 50 (.pack [6]) (.split 51 .done (.split 52 (.pack [2]) (.split 53 (.pack [2]) (.split 63 (.pack [8]) (.split 64 (.pack [9]) (.split 65 (.pack [10]) (.split 76 (.pack [9]) (.split 79 .done (.split 91 (.pack [7]) (.split 118 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 377. -/
theorem checked377 : checkParitySearch 8 (fun q => (rows377 >>> (256*q)) &&& (2^256-1)) 0x81 (allowed377.contains) tree377 0xffeffe5ff5ffffffffffbcbf8bff3fefffdfffaffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 378. -/
noncomputable def rows378 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000006001000c00a0000000080000010011002601200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c00200000000000000000040040000000000000000000036000000000001001200c00000208000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 378. -/
noncomputable def allowed378 : List Nat := [0x10000000000000,0x1000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 378. -/
noncomputable def tree378 : ParitySearchTree := (.split 25 (.pack [2]) (.split 28 (.pack [4]) (.split 37 (.pack [5]) (.split 38 (.pack [6]) (.split 41 (.pack [8]) (.split 52 .done (.split 56 (.pack [9]) (.split 68 (.pack [10]) (.split 95 (.pack [0]) (.split 129 (.pack [8]) (.split 131 (.pack [1]) (.split 142 (.pack [2]) (.split 143 (.pack [3]) (.split 156 .done (.split 169 (.pack [0]) (.split 170 (.pack [0]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 378. -/
theorem checked378 : checkParitySearch 8 (fun q => (rows378 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed378.contains) tree378 0xffeffddffdffffffffffcd7f8bff3ff1ffe7ffeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 379. -/
noncomputable def rows379 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000038000000000000000007007000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 379. -/
noncomputable def allowed379 : List Nat := [0x1,0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 379. -/
noncomputable def tree379 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 .done (.split 12 (.pack [4]) (.split 13 (.pack [6]) (.split 14 (.pack [5]) (.split 87 (.pack [0]) (.split 88 (.pack [1]) (.split 89 (.pack [2]) (.split 129 (.pack [8]) (.split 130 (.pack [8]) (.split 131 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 379. -/
theorem checked379 : checkParitySearch 8 (fun q => (rows379 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed379.contains) tree379 0xffeffdbffbffffffff03fc7fe7ffc7fdffffffdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 380. -/
noncomputable def rows380 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 380. -/
noncomputable def allowed380 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 380. -/
noncomputable def tree380 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 3 .done (.split 4 .done (.split 5 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 380. -/
theorem checked380 : checkParitySearch 8 (fun q => (rows380 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed380.contains) tree380 0xffeffdbffbfffffff81ff3bfe7fe3ffdffffffdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 381. -/
noncomputable def rows381 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000006c000000024000009000100480410000000000120100000000000000000000006000a00000000800c000400a01a00120000000000040000000000000000000000000004006000200c00140090000000000020014034

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 381. -/
noncomputable def allowed381 : List Nat := [0x4,0x80000000000000000000,0x40000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 381. -/
noncomputable def tree381 : ParitySearchTree := (.split 2 .done (.split 4 (.pack [3]) (.split 5 (.pack [4]) (.split 14 (.pack [5]) (.split 16 (.pack [6]) (.split 29 (.pack [7]) (.split 76 (.pack [11]) (.split 79 .done (.split 90 .done (.split 92 (.pack [1]) (.split 106 .done (.split 107 (.pack [2]) (.split 117 (.pack [6]) (.split 133 (.pack [9]) (.split 134 (.pack [8]) (.split 146 (.pack [10]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 381. -/
theorem checked381 : checkParitySearch 8 (fun q => (rows381 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed381.contains) tree381 0xffeffdbffbffffdbffd3fd7fefffe7fdffffffdfd7ffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 382. -/
noncomputable def rows382 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000100000050000000000000000000000800900000000000000000000000004001000200a0014000080000010010003401000240000000000000000000000360000000120000048000002402080000000000900820000000000000000000006005000000004000c00200880130090000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 382. -/
noncomputable def allowed382 : List Nat := [0x20,0x80000000000000000000,0x200000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 382. -/
noncomputable def tree382 : ParitySearchTree := (.split 5 .done (.split 52 (.pack [7]) (.split 55 (.pack [8]) (.split 64 (.pack [7]) (.split 65 (.pack [9]) (.split 68 (.pack [10]) (.split 79 .done (.split 83 (.pack [10]) (.split 93 .done (.split 106 .done (.split 107 (.pack [1]) (.split 122 (.pack [3]) (.split 156 (.pack [4]) (.split 158 (.pack [5]) (.split 169 (.pack [6]) (.split 170 (.pack [2]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 382. -/
theorem checked382 : checkParitySearch 8 (fun q => (rows382 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed382.contains) tree382 0xffeffdbffbffffdbfcdffbbfefff3ffdffffffdfd7fe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 383. -/
noncomputable def rows383 : Nat := 0x40000030000000000000000000000200240000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000001200000b4000000090000012010401201040000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000100000050024000000000000000000800000000000000000000000000030002004000a00a004800000000001801a00020000000000000000000036000010012004004800c0000020800000008000008a

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 383. -/
noncomputable def allowed383 : List Nat := [0x20000,0x80000000000000000000,0x200000000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 383. -/
noncomputable def tree383 : ParitySearchTree := (.split 1 (.pack [3]) (.split 17 .done (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 79 .done (.split 82 (.pack [2]) (.split 93 .done (.split 95 (.pack [6]) (.split 105 .done (.split 107 (.pack [0]) (.split 122 (.pack [0]) (.split 133 (.pack [8]) (.split 148 (.pack [9]) (.split 149 (.pack [9]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 383. -/
theorem checked383 : checkParitySearch 8 (fun q => (rows383 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed383.contains) tree383 0xffeffdbffbffffc9febfffbfebffbffdffffffdfe7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 384. -/
noncomputable def rows384 : Nat := 0x2000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000036000010020000002200a00900208000000080190108

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 384. -/
noncomputable def allowed384 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 384. -/
noncomputable def tree384 : ParitySearchTree := (.split 12 (.pack [1]) (.split 13 (.pack [2]) (.split 14 (.pack [3]) (.split 15 (.pack [4]) (.split 16 (.pack [0]) (.split 17 .done (.split 27 (.pack [6]) (.split 28 (.pack [8]) (.split 29 (.pack [7]) (.split 144 (.pack [10]) (.split 145 (.pack [11]) (.split 146 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 384. -/
theorem checked384 : checkParitySearch 8 (fun q => (rows384 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed384.contains) tree384 0xffeffdbffbffff81fe3fffbffbffbffdffffffdffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 385. -/
noncomputable def rows385 : Nat := 0x3000000000000000100000020024000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000001600500560000000040040008001000808b00000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000a005003600002002c000001004700481040000000100000000000000000000000000000000001000000c00240000000000000000008000000000000000000000000060000000080000000012001801b000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 385. -/
noncomputable def allowed385 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 385. -/
noncomputable def tree385 : ParitySearchTree := (.split 36 (.pack [7]) (.split 37 (.pack [8]) (.split 39 (.pack [9]) (.split 43 (.pack [10]) (.split 51 (.pack [0]) (.split 64 (.pack [13]) (.split 79 .done (.split 94 (.pack [1]) (.split 106 (.pack [3]) (.split 141 (.pack [4]) (.split 142 (.pack [5]) (.split 144 (.pack [6]) (.split 146 (.pack [12]) (.split 156 (.pack [9]) (.split 158 (.pack [2]) (.split 169 (.pack [14]) (.split 170 (.pack [14]) (.split 172 (.pack [15]) (.zero 11)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 385. -/
theorem checked385 : checkParitySearch 8 (fun q => (rows385 >>> (256*q)) &&& (2^256-1)) 0x800 (allowed385.contains) tree385 0xffeffd7ff7ffffffffff9c3f3ffe7fe5ffcfffbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 386. -/
noncomputable def rows386 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000e00000000000000000000000000007007e000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 386. -/
noncomputable def allowed386 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 386. -/
noncomputable def tree386 : ParitySearchTree := (.split 33 (.pack [0]) (.split 34 (.pack [1]) (.split 35 (.pack [2]) (.split 36 (.pack [5]) (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 48 .done (.split 49 .done (.split 50 .done (.split 165 (.pack [7]) (.split 166 (.pack [7]) (.split 167 (.pack [6]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 386. -/
theorem checked386 : checkParitySearch 8 (fun q => (rows386 >>> (256*q)) &&& (2^256-1)) 0x28 (allowed386.contains) tree386 0xffeffd43fa3ffffffffffdbfe7fffffdffffffd1fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 387. -/
noncomputable def rows387 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000240030036000000000008000001000001040000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000004003000c000000004006000800500d00090000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c000000000000000000000080090000000000000000000008019003000610002001402000c008901000240000800000000000000000000006c03c00004804000a800608881710d1000000024000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 387. -/
noncomputable def allowed387 : List Nat := [0x40000000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 387. -/
noncomputable def tree387 : ParitySearchTree := (.split 36 (.pack [4]) (.split 39 (.pack [5]) (.split 52 (.pack [11]) (.split 54 (.pack [10]) (.split 55 (.pack [12]) (.split 64 (.pack [11]) (.split 66 .done (.split 79 .done (.split 93 (.pack [0]) (.split 94 (.pack [1]) (.split 106 (.pack [2]) (.split 142 (.pack [3]) (.split 143 (.pack [8]) (.split 156 (.pack [5]) (.split 157 (.pack [6]) (.split 170 (.pack [9]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 387. -/
theorem checked387 : checkParitySearch 8 (fun q => (rows387 >>> (256*q)) &&& (2^256-1)) 0x81 (allowed387.contains) tree387 0xffeffbfffffffffffefbbeff8bff77ed7fdffffffffc9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 388. -/
noncomputable def rows388 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000024003003600000000000800000100000104000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000000200000030048000000000000000001000000000000000000000002003000c000040008000008001e00d00090000000200000000000000000000028000000030002004000a000804800000000001801a0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 388. -/
noncomputable def allowed388 : List Nat := [0x80000000000000000000,0x200000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 388. -/
noncomputable def tree388 : ParitySearchTree := (.split 5 (.pack [1]) (.split 7 (.pack [3]) (.split 8 (.pack [2]) (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 67 (.pack [1]) (.split 70 (.pack [8]) (.split 79 .done (.split 93 .done (.split 95 (.pack [7]) (.split 110 (.pack [9]) (.split 121 (.pack [5]) (.split 136 (.pack [6]) (.split 137 (.pack [6]) (.split 171 (.pack [9]) (.split 173 (.pack [7]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 388. -/
theorem checked388 : checkParitySearch 8 (fun q => (rows388 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed388.contains) tree388 0xffeffbfffffffffffc9fbabf8bffffed7fdffffffffe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 389. -/
noncomputable def rows389 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000e00000000000000000000000000007007e0000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 389. -/
noncomputable def allowed389 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 389. -/
noncomputable def tree389 : ParitySearchTree := (.split 33 (.pack [0]) (.split 34 (.pack [1]) (.split 35 (.pack [2]) (.split 36 (.pack [5]) (.split 37 (.pack [5]) (.split 38 (.pack [4]) (.split 48 .done (.split 49 .done (.split 50 .done (.split 165 (.pack [7]) (.split 166 (.pack [7]) (.split 167 (.pack [6]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 389. -/
theorem checked389 : checkParitySearch 8 (fun q => (rows389 >>> (256*q)) &&& (2^256-1)) 0x28 (allowed389.contains) tree389 0xffeffb83f63ffffffffffdbfe7fffffeffffffb1fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 390. -/
noncomputable def rows390 : Nat := 0x2000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000038000000000000000007007000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 390. -/
noncomputable def allowed390 : List Nat := [0x1,0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 390. -/
noncomputable def tree390 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 .done (.split 12 (.pack [4]) (.split 13 (.pack [5]) (.split 14 (.pack [6]) (.split 87 (.pack [0]) (.split 88 (.pack [1]) (.split 89 (.pack [2]) (.split 129 (.pack [8]) (.split 130 (.pack [7]) (.split 131 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 390. -/
theorem checked390 : checkParitySearch 8 (fun q => (rows390 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed390.contains) tree390 0xffeffb7ff7ffffffff03fc7fe7ffc7feffffffbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 391. -/
noncomputable def rows391 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 391. -/
noncomputable def allowed391 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 391. -/
noncomputable def tree391 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 3 .done (.split 4 .done (.split 5 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 391. -/
theorem checked391 : checkParitySearch 8 (fun q => (rows391 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed391.contains) tree391 0xffeffb7ff7fffffff81ff3bfe7fe3ffeffffffbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 392. -/
noncomputable def rows392 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000002d000005a00000000000000000000168145000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000006c000000024000009000100480410000000000120100000000000000000000000000004006000200c00140090000000000020014034

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 392. -/
noncomputable def allowed392 : List Nat := [0x4,0x80000000000000000000,0x40000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 392. -/
noncomputable def tree392 : ParitySearchTree := (.split 2 .done (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 14 (.pack [4]) (.split 16 (.pack [5]) (.split 29 (.pack [7]) (.split 76 (.pack [10]) (.split 79 .done (.split 90 .done (.split 92 (.pack [9]) (.split 106 .done (.split 107 (.pack [1]) (.split 117 (.pack [5]) (.split 133 (.pack [7]) (.split 134 (.pack [6]) (.split 146 (.pack [8]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 392. -/
theorem checked392 : checkParitySearch 8 (fun q => (rows392 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed392.contains) tree392 0xffeffb7ff7ffffdbffd3fd7fefffe7feffffffbfd7ffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 393. -/
noncomputable def rows393 : Nat := (Nat.lor 0x400000060000000000000000000002002400000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000001000000500000000000000000000008009000000000000000000000000020002002000c00c00000800000100020160008048000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000000000000000080000028012000000000000000000400000000000000000000000000000000004000003000900000000000000000020000000000000000000000060012000006c4000c00280880120082024020800020000000000000000000000000060060000080080000002013800301b0000000040000000000000000000000000000000000200000180048000000000000000001 (Nat.shiftLeft 0x18000000000000004000000800900000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000000600000000000000100000020024000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 393. -/
noncomputable def allowed393 : List Nat := [0x20,0x80000000000000000000,0x200000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 393. -/
noncomputable def tree393 : ParitySearchTree := (.split 5 .done (.split 23 (.pack [7]) (.split 29 (.pack [12]) (.split 38 (.pack [14]) (.split 41 (.pack [15]) (.split 49 (.pack [13]) (.split 55 (.pack [18]) (.split 65 (.pack [16]) (.split 68 (.pack [17]) (.split 79 .done (.split 83 (.pack [19]) (.split 91 (.pack [0]) (.split 93 .done (.split 106 .done (.split 107 (.pack [1]) (.split 122 (.pack [9]) (.split 126 (.pack [3]) (.split 127 (.pack [4]) (.split 129 (.pack [5]) (.split 130 (.pack [6]) (.split 153 (.pack [10]) (.split 156 (.pack [11]) (.split 169 (.pack [8]) (.split 170 (.pack [15]) (.zero 2)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 393. -/
theorem checked393 : checkParitySearch 8 (fun q => (rows393 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed393.contains) tree393 0xffeffb7ff7ffffdbfcdffbbfefff3ffeffffffbfd7fe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 394. -/
noncomputable def rows394 : Nat := 0x300000000000000080000010012000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000100000050024000000000000000000800000000000000000000000000030002004000a00a004800000000001801a00020000000000000000000036000010012004004800c0000020800000008000008a

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 394. -/
noncomputable def allowed394 : List Nat := [0x20000,0x80000000000000000000,0x200000000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 394. -/
noncomputable def tree394 : ParitySearchTree := (.split 1 (.pack [3]) (.split 17 .done (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 79 .done (.split 82 (.pack [2]) (.split 93 .done (.split 95 (.pack [9]) (.split 105 .done (.split 107 (.pack [0]) (.split 122 (.pack [0]) (.split 133 (.pack [7]) (.split 148 (.pack [8]) (.split 149 (.pack [8]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 394. -/
theorem checked394 : checkParitySearch 8 (fun q => (rows394 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed394.contains) tree394 0xffeffb7ff7ffffc9febfffbfebffbffeffffffbfe7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 395. -/
noncomputable def rows395 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000036000010020000002200a00900208000000080190108

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 395. -/
noncomputable def allowed395 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 395. -/
noncomputable def tree395 : ParitySearchTree := (.split 12 (.pack [1]) (.split 13 (.pack [2]) (.split 14 (.pack [3]) (.split 15 (.pack [4]) (.split 16 (.pack [0]) (.split 17 .done (.split 27 (.pack [6]) (.split 28 (.pack [7]) (.split 29 (.pack [8]) (.split 144 (.pack [10]) (.split 145 (.pack [11]) (.split 146 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 395. -/
theorem checked395 : checkParitySearch 8 (fun q => (rows395 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed395.contains) tree395 0xffeffb7ff7ffff81fe3fffbffbffbffeffffffbffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 396. -/
noncomputable def rows396 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000008002006000c000000006000000c00980400090000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000036000000024001002400c0000020800000000012010c

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 396. -/
noncomputable def allowed396 : List Nat := [0x40000000000000000,0x200000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 396. -/
noncomputable def tree396 : ParitySearchTree := (.split 24 (.pack [3]) (.split 27 (.pack [4]) (.split 42 (.pack [8]) (.split 51 (.pack [10]) (.split 52 (.pack [11]) (.split 55 (.pack [12]) (.split 66 .done (.split 67 (.pack [13]) (.split 93 .done (.split 94 (.pack [0]) (.split 130 (.pack [1]) (.split 131 (.pack [2]) (.split 145 (.pack [5]) (.split 146 (.pack [9]) (.split 157 (.pack [7]) (.split 171 (.pack [13]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 396. -/
theorem checked396 : checkParitySearch 8 (fun q => (rows396 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed396.contains) tree396 0xffeffafffffffffffedfaeff53feffe9ffd7fffffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 397. -/
noncomputable def rows397 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000020001003000600000000a000001400681000240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000024001003200a00140000800000100000114010002400000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000000000a0000000040000000009002802d000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 397. -/
noncomputable def allowed397 : List Nat := [0x40000000000000000,0x200000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 397. -/
noncomputable def tree397 : ParitySearchTree := (.split 26 (.pack [4]) (.split 29 (.pack [6]) (.split 44 (.pack [9]) (.split 51 (.pack [0]) (.split 53 (.pack [0]) (.split 54 (.pack [11]) (.split 66 .done (.split 68 (.pack [12]) (.split 93 .done (.split 95 (.pack [3]) (.split 129 (.pack [1]) (.split 130 (.pack [2]) (.split 144 (.pack [5]) (.split 145 (.pack [10]) (.split 156 (.pack [7]) (.split 173 (.pack [3]) (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 397. -/
theorem checked397 : checkParitySearch 8 (fun q => (rows397 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed397.contains) tree397 0xffeff9bffbfffffffedfbebf8bff7fefffdfffdffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 398. -/
noncomputable def rows398 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000380000000000000000000000000001c01f800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000060000000010000000000001801b0000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 398. -/
noncomputable def allowed398 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 398. -/
noncomputable def tree398 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 .done (.split 17 .done (.split 18 (.pack [1]) (.split 19 (.pack [2]) (.split 20 (.pack [3]) (.split 30 (.pack [7]) (.split 31 (.pack [5]) (.split 32 (.pack [6]) (.split 147 (.pack [9]) (.split 148 (.pack [10]) (.split 149 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 398. -/
theorem checked398 : checkParitySearch 8 (fun q => (rows398 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed398.contains) tree398 0xffeff6ffefffff81ff1ffdbffbffffe77fffff7ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 399. -/
noncomputable def rows399 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000030001006000a000000008000001000a01a001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c00200000000000000000040040000000000000000000036000000000001001200c00000208000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 399. -/
noncomputable def allowed399 : List Nat := [0x80000000000000,0x1000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 399. -/
noncomputable def tree399 : ParitySearchTree := (.split 25 (.pack [2]) (.split 28 (.pack [3]) (.split 41 (.pack [6]) (.split 43 (.pack [7]) (.split 44 (.pack [8]) (.split 53 (.pack [9]) (.split 55 .done (.split 68 (.pack [10]) (.split 95 (.pack [0]) (.split 129 (.pack [6]) (.split 131 (.pack [1]) (.split 145 (.pack [3]) (.split 146 (.pack [4]) (.split 156 .done (.split 172 (.pack [10]) (.split 173 (.pack [0]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 399. -/
theorem checked399 : checkParitySearch 8 (fun q => (rows399 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed399.contains) tree399 0xffeff5ffefffffffffffcd7f8bff3feaffe7ff7ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 400. -/
noncomputable def rows400 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000060000000010000000000001801b0000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 400. -/
noncomputable def allowed400 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 400. -/
noncomputable def tree400 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 .done (.split 17 .done (.split 18 (.pack [1]) (.split 19 (.pack [2]) (.split 20 (.pack [3]) (.split 30 (.pack [5]) (.split 31 (.pack [7]) (.split 32 (.pack [6]) (.split 147 (.pack [9]) (.split 148 (.pack [10]) (.split 149 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 400. -/
theorem checked400 : checkParitySearch 8 (fun q => (rows400 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed400.contains) tree400 0xffefedffdfffff81ff1ffdbffbffffeb7ffffefffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 401. -/
noncomputable def rows401 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000018004003000c000000004000000800500d00090000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400100000000000000000020020000000000000000000036000000000001001200c00000208000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 401. -/
noncomputable def allowed401 : List Nat := [0x40000000000000,0x4000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 401. -/
noncomputable def tree401 : ParitySearchTree := (.split 24 (.pack [2]) (.split 27 (.pack [3]) (.split 40 (.pack [6]) (.split 42 (.pack [7]) (.split 43 (.pack [8]) (.split 52 (.pack [9]) (.split 54 .done (.split 67 (.pack [10]) (.split 94 (.pack [0]) (.split 130 (.pack [1]) (.split 131 (.pack [6]) (.split 144 (.pack [3]) (.split 145 (.pack [4]) (.split 158 .done (.split 171 (.pack [10]) (.split 172 (.pack [0]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 401. -/
theorem checked401 : checkParitySearch 8 (fun q => (rows401 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed401.contains) tree401 0xffefdeffbfffffffffffacff53febfe5ffd7fdfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 402. -/
noncomputable def rows402 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000060000000010000000000001801b0000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 402. -/
noncomputable def allowed402 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 402. -/
noncomputable def tree402 : ParitySearchTree := (.split 15 (.pack [0]) (.split 16 .done (.split 17 .done (.split 18 (.pack [1]) (.split 19 (.pack [2]) (.split 20 (.pack [3]) (.split 30 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 147 (.pack [9]) (.split 148 (.pack [10]) (.split 149 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 402. -/
theorem checked402 : checkParitySearch 8 (fun q => (rows402 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed402.contains) tree402 0xffefdbffbfffff81ff1ffdbffbfffff37ffffdfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 403. -/
noncomputable def rows403 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 403. -/
noncomputable def allowed403 : List Nat := [0x40000000000000,0x80000000000000,0x100000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 403. -/
noncomputable def tree403 : ParitySearchTree := (.split 54 .done (.split 55 .done (.split 56 .done (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 69 (.pack [7]) (.split 70 (.pack [8]) (.split 71 (.pack [9]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 403. -/
theorem checked403 : checkParitySearch 8 (fun q => (rows403 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed403.contains) tree403 0xffefc47f87fffffffffffdbfe7fffffefffffc3ffffff 0 1 = true := by decide +kernel

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

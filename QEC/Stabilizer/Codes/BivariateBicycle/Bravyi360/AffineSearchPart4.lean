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
/-- Packed parity neighborhoods for affine fiber 404. -/
noncomputable def rows404 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 404. -/
noncomputable def allowed404 : List Nat := [0x40000000000000,0x80000000000000,0x100000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 404. -/
noncomputable def tree404 : ParitySearchTree := (.split 54 .done (.split 55 .done (.split 56 .done (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 69 (.pack [7]) (.split 70 (.pack [8]) (.split 71 (.pack [9]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 404. -/
theorem checked404 : checkParitySearch 8 (fun q => (rows404 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed404.contains) tree404 0xffefc2bf8bfffffffffffdbfe7fffffdfffffc5ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 405. -/
noncomputable def rows405 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 405. -/
noncomputable def allowed405 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 405. -/
noncomputable def tree405 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [4]) (.split 17 (.pack [5]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [6]) (.split 134 (.pack [6]) (.split 169 (.pack [7]) (.split 170 (.pack [2]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 405. -/
theorem checked405 : checkParitySearch 8 (fun q => (rows405 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed405.contains) tree405 0xffefbfffffbfffffff03fe3ffffff1ff9ffedffdfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 406. -/
noncomputable def rows406 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000006400a0074000000040008008008000801940000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 406. -/
noncomputable def allowed406 : List Nat := [0x400000000,0x40000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 406. -/
noncomputable def tree406 : ParitySearchTree := (.split 34 .done (.split 36 (.pack [4]) (.split 39 (.pack [5]) (.split 40 (.pack [6]) (.split 51 (.pack [10]) (.split 67 (.pack [11]) (.split 79 (.pack [1]) (.split 91 (.pack [0]) (.split 106 (.pack [2]) (.split 138 .done (.split 140 (.pack [7]) (.split 141 (.pack [3]) (.split 142 (.pack [9]) (.split 153 (.pack [4]) (.split 155 (.pack [10]) (.split 166 (.pack [12]) (.split 169 (.pack [13]) (.split 170 (.pack [9]) (.zero 8)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 406. -/
theorem checked406 : checkParitySearch 8 (fun q => (rows406 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed406.contains) tree406 0xffefbffff7d7ff7fdffffffbffffc9ff9ffd7ffbff6bf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 407. -/
noncomputable def rows407 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000001c0000000000000000000000000000e00fc0000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 407. -/
noncomputable def allowed407 : List Nat := [0x200000000000,0x400000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 407. -/
noncomputable def tree407 : ParitySearchTree := (.split 42 (.pack [0]) (.split 43 (.pack [1]) (.split 44 (.pack [2]) (.split 45 .done (.split 46 .done (.split 47 .done (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 174 (.pack [8]) (.split 175 (.pack [8]) (.split 176 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 407. -/
theorem checked407 : checkParitySearch 8 (fun q => (rows407 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed407.contains) tree407 0xffefbfc47fc7ffffffffffffffffc9fffffedffe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 408. -/
noncomputable def rows408 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 408. -/
noncomputable def allowed408 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 408. -/
noncomputable def tree408 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 408. -/
theorem checked408 : checkParitySearch 8 (fun q => (rows408 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed408.contains) tree408 0xffefb7ff7fffff81ff1ffdbffbffff3f7ffffbfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 409. -/
noncomputable def rows409 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 409. -/
noncomputable def allowed409 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 409. -/
noncomputable def tree409 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 409. -/
theorem checked409 : checkParitySearch 8 (fun q => (rows409 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed409.contains) tree409 0xffef6ffeffffff81ff1ffdbffbffff5f7ffff7fffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 410. -/
noncomputable def rows410 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000800c0004018002800000000000000400280680048000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000200000030048000000000000000001000000000000000000000006600a00000000800d00040080184012000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 410. -/
noncomputable def allowed410 : List Nat := [0x4000000000000000,0x400000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 410. -/
noncomputable def tree410 : ParitySearchTree := (.split 19 (.pack [2]) (.split 22 (.pack [3]) (.split 35 (.pack [6]) (.split 37 (.pack [7]) (.split 38 (.pack [8]) (.split 47 (.pack [9]) (.split 49 (.pack [10]) (.split 62 .done (.split 123 (.pack [6]) (.split 125 (.pack [1]) (.split 139 (.pack [3]) (.split 140 (.pack [4]) (.split 150 (.pack [10]) (.split 166 .done (.split 167 (.pack [0]) (.split 179 (.pack [11]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 410. -/
theorem checked410 : checkParitySearch 8 (fun q => (rows410 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed410.contains) tree410 0xffef3ff7ffbffffffff6ff57fd7fceffbffe9ffdfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 411. -/
noncomputable def rows411 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000c00400100140028000000000000006004c0200048000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 411. -/
noncomputable def allowed411 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 411. -/
noncomputable def tree411 : ParitySearchTree := (.split 19 (.pack [2]) (.split 22 (.pack [3]) (.split 37 (.pack [7]) (.split 46 (.pack [10]) (.split 47 (.pack [8]) (.split 50 (.pack [9]) (.split 61 .done (.split 62 .done (.split 123 (.pack [0]) (.split 125 (.pack [1]) (.split 138 (.pack [9]) (.split 140 (.pack [4]) (.split 152 (.pack [6]) (.split 166 .done (.split 178 .done (.split 179 (.pack [11]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 411. -/
theorem checked411 : checkParitySearch 8 (fun q => (rows411 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed411.contains) tree411 0xffef3fd3fffffffffff6ff57fd7fceffdffe9ffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 412. -/
noncomputable def rows412 : Nat := 0x50000000000000004000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000004000600c000000004000c0080088013009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002402000d80c00000900800120004168001048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 412. -/
noncomputable def allowed412 : List Nat := [0x8000000000000000,0x80000000000000000000,0x40000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 412. -/
noncomputable def tree412 : ParitySearchTree := (.split 36 (.pack [2]) (.split 39 (.pack [5]) (.split 48 (.pack [6]) (.split 49 (.pack [7]) (.split 52 (.pack [10]) (.split 63 .done (.split 67 (.pack [10]) (.split 79 .done (.split 90 .done (.split 91 (.pack [4]) (.split 106 (.pack [0]) (.split 142 (.pack [1]) (.split 143 (.pack [9]) (.split 153 (.pack [2]) (.split 154 (.pack [3]) (.split 170 .done (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 412. -/
theorem checked412 : checkParitySearch 8 (fun q => (rows412 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed412.contains) tree412 0xffeeff6fffffffffffdbf4ffebffecfd7ffb7fffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 413. -/
noncomputable def rows413 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c0000400000080080032020004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000024806006d8000200248080001060200820100000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 413. -/
noncomputable def allowed413 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 413. -/
noncomputable def tree413 : ParitySearchTree := (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 .done (.split 67 (.pack [11]) (.split 79 .done (.split 91 (.pack [0]) (.split 106 (.pack [1]) (.split 141 (.pack [2]) (.split 142 (.pack [3]) (.split 153 (.pack [5]) (.split 155 .done (.split 169 (.pack [4]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 413. -/
theorem checked413 : checkParitySearch 8 (fun q => (rows413 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed413.contains) tree413 0xffeefbeff7fffffffffff4bfebffe4fcfffb7fbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 414. -/
noncomputable def rows414 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 414. -/
noncomputable def allowed414 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 414. -/
noncomputable def tree414 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 414. -/
theorem checked414 : checkParitySearch 8 (fun q => (rows414 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed414.contains) tree414 0xffeedffdffffff81ff1ffdbffbffff9f7fffeffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 415. -/
noncomputable def rows415 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000006400a007400000004000800800800080194000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000200000180000000000000000000001001200000000000000000000000080040068018003000010010002000002180100024000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 415. -/
noncomputable def allowed415 : List Nat := [0x400000000,0x40000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 415. -/
noncomputable def tree415 : ParitySearchTree := (.split 34 .done (.split 36 (.pack [5]) (.split 39 (.pack [6]) (.split 40 (.pack [7]) (.split 51 (.pack [10]) (.split 67 (.pack [11]) (.split 79 (.pack [1]) (.split 91 (.pack [0]) (.split 106 (.pack [2]) (.split 138 .done (.split 140 (.pack [4]) (.split 141 (.pack [3]) (.split 142 (.pack [9]) (.split 153 (.pack [5]) (.split 155 (.pack [10]) (.split 166 (.pack [12]) (.split 169 (.pack [13]) (.split 170 (.pack [9]) (.zero 8)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 415. -/
theorem checked415 : checkParitySearch 8 (fun q => (rows415 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed415.contains) tree415 0xffedfffbf7d7ff7fdffffffbffffcfff9ffd5ffbff6bf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 416. -/
noncomputable def rows416 : Nat := (Nat.lor 0x280000000000000020000004004800000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000004000000600000000000000000000020024000000000000000000002e0000000320000046000005805300000000001901a2000000000000000000002e000000009000004000000580530000000000048041000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0x18000000000000004000000800900000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 416. -/
noncomputable def allowed416 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 416. -/
noncomputable def tree416 : ParitySearchTree := (.split 1 .done (.split 5 (.pack [5]) (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 16 (.pack [6]) (.split 19 (.pack [7]) (.split 20 (.pack [8]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 68 (.pack [14]) (.split 70 (.pack [15]) (.split 79 (.pack [3]) (.split 80 (.pack [3]) (.split 82 (.pack [1]) (.split 105 (.pack [5]) (.split 106 (.pack [5]) (.split 110 (.pack [16]) (.split 133 (.pack [9]) (.split 136 (.pack [10]) (.split 137 (.pack [10]) (.split 169 (.pack [11]) (.split 170 (.pack [12]) (.split 171 (.pack [16]) (.split 173 (.pack [13]) (.zero 4)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 416. -/
theorem checked416 : checkParitySearch 8 (fun q => (rows416 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed416.contains) tree416 0xffedffdffffffffffc63f83fffff37fffffefffffffe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 417. -/
noncomputable def rows417 : Nat := (Nat.lor 0x180000000000000040000008009000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000004000000600000000000000000000020024000000000000000000000001e000000034000002a000009808b00000000001a01940000000000000000000000000000002000000a00000000000000000000010012000000000000000000001e0000000090000020000009808b0000000000048041000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0x28000000000000002000000400480000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 417. -/
noncomputable def allowed417 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 417. -/
noncomputable def tree417 : ParitySearchTree := (.split 2 .done (.split 4 (.pack [4]) (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 17 (.pack [6]) (.split 19 (.pack [7]) (.split 20 (.pack [8]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [14]) (.split 71 (.pack [15]) (.split 79 (.pack [3]) (.split 80 (.pack [3]) (.split 83 (.pack [2]) (.split 105 (.pack [4]) (.split 107 (.pack [4]) (.split 109 (.pack [16]) (.split 134 (.pack [9]) (.split 136 (.pack [10]) (.split 137 (.pack [10]) (.split 169 (.pack [11]) (.split 170 (.pack [12]) (.split 171 (.pack [16]) (.split 172 (.pack [13]) (.zero 5)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 417. -/
theorem checked417 : checkParitySearch 8 (fun q => (rows417 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed417.contains) tree417 0xffedffdffffffffffaa3f43ffffeb7fffffefffffffd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 418. -/
noncomputable def rows418 : Nat := (Nat.lor 0x28000000000000002000000400480000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000036000000036000000000000d80c300000000001b0186000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000028005000020004001000200d004000900000001001000000000000000000000018003000010002001000200c808001200000000800800000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0x300000000000000010000002002400000000000000000000000000000000000000018000000000000004000000800900000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 418. -/
noncomputable def allowed418 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 418. -/
noncomputable def tree418 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 7 (.pack [3]) (.split 8 (.pack [4]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 19 (.pack [8]) (.split 20 (.pack [9]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 70 (.pack [15]) (.split 71 (.pack [16]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 82 (.pack [3]) (.split 83 (.pack [4]) (.split 133 (.pack [10]) (.split 134 (.pack [10]) (.split 136 (.pack [11]) (.split 137 (.pack [11]) (.split 169 (.pack [12]) (.split 170 (.pack [13]) (.split 172 (.pack [14]) (.split 173 (.pack [17]) (.zero 5)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 418. -/
theorem checked418 : checkParitySearch 8 (fun q => (rows418 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed418.contains) tree418 0xffedffdffffffffff9c3f23ffffe77fffffefffffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 419. -/
noncomputable def rows419 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000036000000030000000c00000d80c300000000001801b00000000000000000000036000000008000000c00000d80c300000000000400480000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 419. -/
noncomputable def allowed419 : List Nat := [0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 419. -/
noncomputable def tree419 : ParitySearchTree := (.split 4 .done (.split 5 .done (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 19 (.pack [6]) (.split 20 (.pack [7]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 70 (.pack [12]) (.split 71 (.pack [13]) (.split 79 (.pack [4]) (.split 80 (.pack [4]) (.split 82 (.pack [1]) (.split 83 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [3]) (.split 136 (.pack [8]) (.split 137 (.pack [8]) (.split 169 (.pack [9]) (.split 170 (.pack [10]) (.split 172 (.pack [11]) (.split 173 (.pack [4]) (.zero 5)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 419. -/
theorem checked419 : checkParitySearch 8 (fun q => (rows419 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed419.contains) tree419 0xffedffdffffffffff8c7f07ffffe3ffffffeffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 420. -/
noncomputable def rows420 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f8000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 420. -/
noncomputable def allowed420 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 420. -/
noncomputable def tree420 : ParitySearchTree := (.split 3 .done (.split 4 .done (.split 5 .done (.split 6 (.pack [0]) (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 18 (.pack [4]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 135 (.pack [8]) (.split 136 (.pack [9]) (.split 137 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 420. -/
theorem checked420 : checkParitySearch 8 (fun q => (rows420 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed420.contains) tree420 0xffedffdffffffffff88ff0fffffe2ffffffeffffffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 421. -/
noncomputable def rows421 : Nat := 0x1000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000380000000000000000000000000001c01f8000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 421. -/
noncomputable def allowed421 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 421. -/
noncomputable def tree421 : ParitySearchTree := (.split 3 .done (.split 4 .done (.split 5 .done (.split 6 (.pack [0]) (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 18 (.pack [4]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 135 (.pack [8]) (.split 136 (.pack [9]) (.split 137 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 421. -/
theorem checked421 : checkParitySearch 8 (fun q => (rows421 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed421.contains) tree421 0xffedffdffffffffff857f17ffffe1ffffffeffffffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 422. -/
noncomputable def rows422 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 422. -/
noncomputable def allowed422 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 422. -/
noncomputable def tree422 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 422. -/
theorem checked422 : checkParitySearch 8 (fun q => (rows422 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed422.contains) tree422 0xffedffdffffffffff603ee3ffffdf7fffffeffffffe7f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 423. -/
noncomputable def rows423 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 423. -/
noncomputable def allowed423 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 423. -/
noncomputable def tree423 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 423. -/
theorem checked423 : checkParitySearch 8 (fun q => (rows423 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed423.contains) tree423 0xffedffdfffffffffed03de3ffffbf7fffffeffffffebf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 424. -/
noncomputable def rows424 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 424. -/
noncomputable def allowed424 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 424. -/
noncomputable def tree424 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 424. -/
theorem checked424 : checkParitySearch 8 (fun q => (rows424 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed424.contains) tree424 0xffedffdfffffffffdb03be3ffff7f7fffffefffffff3f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 425. -/
noncomputable def rows425 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 425. -/
noncomputable def allowed425 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 425. -/
noncomputable def tree425 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 425. -/
theorem checked425 : checkParitySearch 8 (fun q => (rows425 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed425.contains) tree425 0xffedffdfffffffffb7037e3fffeff7fffffeffffff3ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 426. -/
noncomputable def rows426 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 426. -/
noncomputable def allowed426 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 426. -/
noncomputable def tree426 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 426. -/
theorem checked426 : checkParitySearch 8 (fun q => (rows426 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed426.contains) tree426 0xffedffdfffffffff6f02fe3fffdff7fffffeffffff5ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 427. -/
noncomputable def rows427 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 427. -/
noncomputable def allowed427 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 427. -/
noncomputable def tree427 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 427. -/
theorem checked427 : checkParitySearch 8 (fun q => (rows427 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed427.contains) tree427 0xffedffdffffffffedf01fe3fffbff7fffffeffffff9ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 428. -/
noncomputable def rows428 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000008000000c00200000000000000000040040000000000000000000a00c00000c004001000c0000022036000000006004c0200000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 428. -/
noncomputable def allowed428 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 428. -/
noncomputable def tree428 : ParitySearchTree := (.split 1 .done (.split 10 (.pack [0]) (.split 11 (.pack [1]) (.split 14 (.pack [3]) (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 61 (.pack [13]) (.split 62 (.pack [14]) (.split 64 (.pack [4]) (.split 65 (.pack [4]) (.split 73 (.pack [13]) (.split 77 (.pack [15]) (.split 102 (.pack [3]) (.split 103 (.pack [3]) (.split 116 (.pack [15]) (.split 130 (.pack [7]) (.split 142 (.pack [11]) (.split 143 (.pack [10]) (.split 166 (.pack [8]) (.split 167 (.pack [9]) (.split 177 (.pack [15]) (.split 179 (.pack [12]) (.zero 2)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 428. -/
theorem checked428 : checkParitySearch 8 (fun q => (rows428 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed428.contains) tree428 0xffedffdffffffff93f0ffe3ffe7ff7fffffefffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 429. -/
noncomputable def rows429 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000060000000010000000000001801b00000000000080090000000000000000000600c00000c00800080140000014036000000006002c04000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 429. -/
noncomputable def allowed429 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 429. -/
noncomputable def tree429 : ParitySearchTree := (.split 2 .done (.split 10 (.pack [0]) (.split 11 (.pack [1]) (.split 13 (.pack [2]) (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 61 (.pack [13]) (.split 62 (.pack [14]) (.split 64 (.pack [4]) (.split 65 (.pack [4]) (.split 74 (.pack [14]) (.split 76 (.pack [15]) (.split 102 (.pack [2]) (.split 104 (.pack [2]) (.split 115 (.pack [15]) (.split 131 (.pack [7]) (.split 142 (.pack [11]) (.split 143 (.pack [10]) (.split 166 (.pack [8]) (.split 167 (.pack [9]) (.split 177 (.pack [15]) (.split 178 (.pack [12]) (.zero 3)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 429. -/
theorem checked429 : checkParitySearch 8 (fun q => (rows429 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed429.contains) tree429 0xffedffdffffffff4bf17fe3ffd7ff7fffffefffffafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 430. -/
noncomputable def rows430 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 430. -/
noncomputable def allowed430 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 430. -/
noncomputable def tree430 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 430. -/
theorem checked430 : checkParitySearch 8 (fun q => (rows430 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed430.contains) tree430 0xffedffdffffffff27f1bfe3ffcfff7fffffefffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 431. -/
noncomputable def rows431 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 431. -/
noncomputable def allowed431 : List Nat := [0x2000,0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 431. -/
noncomputable def tree431 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 .done (.split 14 .done (.split 15 (.pack [2]) (.split 16 (.pack [3]) (.split 17 (.pack [4]) (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 1)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 431. -/
theorem checked431 : checkParitySearch 8 (fun q => (rows431 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed431.contains) tree431 0xffedffdffffffff03f3bfe7ffc7ffffffffeffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 432. -/
noncomputable def rows432 : Nat := 0x3000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000060000300060060000000001801b000000018018003600000000000000000000060000000010000000000001801b00000000000080090000000000000000000000c0000000020000000000803003600000000000100100000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 432. -/
noncomputable def allowed432 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 432. -/
noncomputable def tree432 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 31 (.pack [8]) (.split 32 (.pack [9]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [12]) (.split 68 (.pack [13]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 121 (.pack [0]) (.split 122 (.pack [1]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.split 148 (.pack [11]) (.split 149 (.pack [11]) (.split 169 (.pack [10]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 432. -/
theorem checked432 : checkParitySearch 8 (fun q => (rows432 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed432.contains) tree432 0xffedffdfffffffefbf27fe3ffb7ff7fffffeffffc9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 433. -/
noncomputable def rows433 : Nat := (Nat.lor 0x80000060000000000000000000000400480000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000100000018024000000000000000000800000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000001000000c002400000000000000000080000000000000000000a020008044041802400000100420f00250080252008260000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0x14000000000000001000000200240000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 433. -/
noncomputable def allowed433 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 433. -/
noncomputable def tree433 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 5 (.pack [3]) (.split 11 (.pack [5]) (.split 21 (.pack [6]) (.split 24 (.pack [10]) (.split 26 (.pack [9]) (.split 29 (.pack [11]) (.split 39 (.pack [10]) (.split 48 (.pack [16]) (.split 50 (.pack [13]) (.split 53 (.pack [20]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 66 (.pack [18]) (.split 67 (.pack [19]) (.split 73 (.pack [21]) (.split 78 (.pack [2]) (.split 88 (.pack [4]) (.split 114 (.pack [7]) (.split 117 (.pack [8]) (.split 127 (.pack [4]) (.split 128 (.pack [5]) (.split 134 (.pack [12]) (.split 142 (.pack [7]) (.split 146 (.pack [15]) (.split 155 (.pack [9]) (.split 169 (.pack [14]) (.split 177 (.pack [16]) (.split 179 (.pack [17]) (.zero 1)))))))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 433. -/
theorem checked433 : checkParitySearch 8 (fun q => (rows433 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed433.contains) tree433 0xffedffdfffffffdf7f4bfe3ff6fff7fffffeffffd2fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 434. -/
noncomputable def rows434 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000040000006000000000000000000000200240000000000000000000000c00000000c000000000300300360000000000060060000000000000000000000c00000000200000000008030036000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 434. -/
noncomputable def allowed434 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 434. -/
noncomputable def tree434 : ParitySearchTree := (.split 1 .done (.split 2 (.pack [2]) (.split 13 (.pack [3]) (.split 14 (.pack [4]) (.split 61 (.pack [7]) (.split 62 (.pack [8]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 76 (.pack [9]) (.split 77 (.pack [10]) (.split 88 (.pack [9]) (.split 89 (.pack [10]) (.split 130 (.pack [5]) (.split 131 (.pack [5]) (.split 166 (.pack [6]) (.split 167 (.pack [0]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 434. -/
theorem checked434 : checkParitySearch 8 (fun q => (rows434 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed434.contains) tree434 0xffedffdfffffffc9ff63fe3ff3fff7fffffeffffe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 435. -/
noncomputable def rows435 : Nat := (Nat.lor 0x20000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000001000000c002400000000000000000080000000000000000000002000800c041804000000000500f00250080012200260000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0xa00000000000000080000010012000000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 435. -/
noncomputable def allowed435 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 435. -/
noncomputable def tree435 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 5 (.pack [5]) (.split 17 (.pack [8]) (.split 21 (.pack [6]) (.split 24 (.pack [10]) (.split 39 (.pack [10]) (.split 48 (.pack [15]) (.split 50 (.pack [12]) (.split 53 (.pack [18]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 66 (.pack [16]) (.split 67 (.pack [17]) (.split 76 (.pack [19]) (.split 78 (.pack [2]) (.split 118 (.pack [8]) (.split 127 (.pack [3]) (.split 128 (.pack [4]) (.split 134 (.pack [11]) (.split 142 (.pack [14]) (.split 143 (.pack [7]) (.split 155 (.pack [9]) (.split 169 (.pack [13]) (.zero 1)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 435. -/
theorem checked435 : checkParitySearch 8 (fun q => (rows435 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed435.contains) tree435 0xffedffdfffffffbeff93fe3fedfff7fffffeffffe4fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 436. -/
noncomputable def rows436 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000c00000000c000000000300300360000000000060060000000000000000000000c00000000200000000008030036000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 436. -/
noncomputable def allowed436 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 436. -/
noncomputable def tree436 : ParitySearchTree := (.split 1 (.pack [2]) (.split 2 .done (.split 13 (.pack [3]) (.split 14 (.pack [4]) (.split 61 (.pack [7]) (.split 62 (.pack [8]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 76 (.pack [9]) (.split 77 (.pack [10]) (.split 88 (.pack [9]) (.split 89 (.pack [10]) (.split 130 (.pack [5]) (.split 131 (.pack [5]) (.split 166 (.pack [6]) (.split 167 (.pack [0]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 436. -/
theorem checked436 : checkParitySearch 8 (fun q => (rows436 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed436.contains) tree436 0xffedffdfffffffa5ffa3fe3febfff7fffffeffffd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 437. -/
noncomputable def rows437 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000c00000000c000000000300300360000000000060060000000000000000000000c00000000200000000008030036000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 437. -/
noncomputable def allowed437 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 437. -/
noncomputable def tree437 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 13 (.pack [2]) (.split 14 (.pack [3]) (.split 61 (.pack [6]) (.split 62 (.pack [7]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 76 (.pack [8]) (.split 77 (.pack [9]) (.split 88 (.pack [8]) (.split 89 (.pack [9]) (.split 130 (.pack [4]) (.split 131 (.pack [4]) (.split 166 (.pack [5]) (.split 167 (.pack [0]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 437. -/
theorem checked437 : checkParitySearch 8 (fun q => (rows437 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed437.contains) tree437 0xffedffdfffffff93ffc3fe3fe7fff7fffffeffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 438. -/
noncomputable def rows438 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 438. -/
noncomputable def allowed438 : List Nat := [0x10000,0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 438. -/
noncomputable def tree438 : ParitySearchTree := (.split 12 (.pack [1]) (.split 13 (.pack [2]) (.split 14 (.pack [3]) (.split 15 (.pack [0]) (.split 16 .done (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 438. -/
theorem checked438 : checkParitySearch 8 (fun q => (rows438 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed438.contains) tree438 0xffedffdfffffff81ffc7fe7fe3fffffffffeffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 439. -/
noncomputable def rows439 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 439. -/
noncomputable def allowed439 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 439. -/
noncomputable def tree439 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 439. -/
theorem checked439 : checkParitySearch 8 (fun q => (rows439 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed439.contains) tree439 0xffedffdfffb7ff7fff03fe3ffffff7fffffe3ffffffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 440. -/
noncomputable def rows440 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 440. -/
noncomputable def allowed440 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 440. -/
noncomputable def tree440 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 440. -/
theorem checked440 : checkParitySearch 8 (fun q => (rows440 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed440.contains) tree440 0xffedffd6ffefffffff03fe3ffffff7fff5feffff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 441. -/
noncomputable def rows441 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 441. -/
noncomputable def allowed441 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 441. -/
noncomputable def tree441 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 441. -/
theorem checked441 : checkParitySearch 8 (fun q => (rows441 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed441.contains) tree441 0xffedffcdffdfffffff03fe3ffffff7fff9fefffefffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 442. -/
noncomputable def rows442 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b00000000000080090000000000000000000000c0000000020000000000803003600000000000100100000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 442. -/
noncomputable def allowed442 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 442. -/
noncomputable def tree442 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 442. -/
theorem checked442 : checkParitySearch 8 (fun q => (rows442 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed442.contains) tree442 0xffedff97ff7fffffff03fe3ffffff7ffaffefffbfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 443. -/
noncomputable def rows443 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b00000000000080090000000000000000000000c0000000020000000000803003600000000000100100000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 443. -/
noncomputable def allowed443 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 443. -/
noncomputable def tree443 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 443. -/
theorem checked443 : checkParitySearch 8 (fun q => (rows443 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed443.contains) tree443 0xffedff4ffeffffffff03fe3ffffff7ffcffefff7fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 444. -/
noncomputable def rows444 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000006000000000000000c001c018018803f0000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 444. -/
noncomputable def allowed444 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 444. -/
noncomputable def tree444 : ParitySearchTree := (.split 48 .done (.split 49 .done (.split 50 .done (.split 51 (.pack [5]) (.split 52 (.pack [6]) (.split 53 (.pack [7]) (.split 63 (.pack [8]) (.split 67 (.pack [6]) (.split 68 (.pack [7]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 90 (.pack [0]) (.split 91 (.pack [1]) (.split 92 (.pack [0]) (.split 106 (.pack [2]) (.split 107 (.pack [2]) (.split 169 (.pack [3]) (.split 170 (.pack [9]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 444. -/
theorem checked444 : checkParitySearch 8 (fun q => (rows444 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed444.contains) tree444 0xffedff31fe1fffffffffffffffffcffff9fefff0fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 445. -/
noncomputable def rows445 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000006000000000000000c001c018018803f0000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 445. -/
noncomputable def allowed445 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 445. -/
noncomputable def tree445 : ParitySearchTree := (.split 48 .done (.split 49 .done (.split 50 .done (.split 51 (.pack [5]) (.split 52 (.pack [6]) (.split 53 (.pack [7]) (.split 63 (.pack [8]) (.split 67 (.pack [6]) (.split 68 (.pack [7]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 90 (.pack [0]) (.split 91 (.pack [1]) (.split 92 (.pack [0]) (.split 106 (.pack [2]) (.split 107 (.pack [2]) (.split 169 (.pack [3]) (.split 170 (.pack [9]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 445. -/
theorem checked445 : checkParitySearch 8 (fun q => (rows445 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed445.contains) tree445 0xffedff2afe2fffffffffffffffffcffff5fefff17ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 446. -/
noncomputable def rows446 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000006000000000000000c001c018018803f0000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 446. -/
noncomputable def allowed446 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 446. -/
noncomputable def tree446 : ParitySearchTree := (.split 48 .done (.split 49 .done (.split 50 .done (.split 51 (.pack [5]) (.split 52 (.pack [6]) (.split 53 (.pack [7]) (.split 63 (.pack [8]) (.split 67 (.pack [6]) (.split 68 (.pack [7]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 90 (.pack [0]) (.split 91 (.pack [1]) (.split 92 (.pack [0]) (.split 106 (.pack [2]) (.split 107 (.pack [2]) (.split 169 (.pack [3]) (.split 170 (.pack [9]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 446. -/
theorem checked446 : checkParitySearch 8 (fun q => (rows446 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed446.contains) tree446 0xffedff277e37ffffffffffffffffcffff3fefff1bffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 447. -/
noncomputable def rows447 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000000040000030000000000000000000000200240000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 447. -/
noncomputable def allowed447 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 447. -/
noncomputable def tree447 : ParitySearchTree := (.split 45 (.pack [0]) (.split 46 (.pack [1]) (.split 47 (.pack [2]) (.split 48 .done (.split 49 .done (.split 50 .done (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 177 (.pack [8]) (.split 178 (.pack [8]) (.split 179 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 447. -/
theorem checked447 : checkParitySearch 8 (fun q => (rows447 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed447.contains) tree447 0xffedff23fe77ff7fffffffffffffcffffffe3ff1fffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 448. -/
noncomputable def rows448 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 448. -/
noncomputable def allowed448 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 448. -/
noncomputable def tree448 : ParitySearchTree := (.split 45 (.pack [0]) (.split 46 (.pack [1]) (.split 47 (.pack [2]) (.split 48 .done (.split 49 .done (.split 50 .done (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 177 (.pack [8]) (.split 178 (.pack [8]) (.split 179 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 448. -/
theorem checked448 : checkParitySearch 8 (fun q => (rows448 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed448.contains) tree448 0xffedff23fe3fffffffb7ff7fffffdffffffefff1ffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 449. -/
noncomputable def rows449 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 449. -/
noncomputable def allowed449 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 449. -/
noncomputable def tree449 : ParitySearchTree := (.split 45 (.pack [0]) (.split 46 (.pack [1]) (.split 47 (.pack [2]) (.split 48 .done (.split 49 .done (.split 50 .done (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 177 (.pack [8]) (.split 178 (.pack [8]) (.split 179 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 449. -/
theorem checked449 : checkParitySearch 8 (fun q => (rows449 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed449.contains) tree449 0xffedff23fe3fffffff6ffeffffffeffffffefff1ffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 450. -/
noncomputable def rows450 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b00000000000080090000000000000000000000c0000000020000000000803003600000000000100100000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 450. -/
noncomputable def allowed450 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 450. -/
noncomputable def tree450 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 450. -/
theorem checked450 : checkParitySearch 8 (fun q => (rows450 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed450.contains) tree450 0xffedfd9ffbffffffff03fe3ffffff7fd7ffeffdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 451. -/
noncomputable def rows451 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b00000000000080090000000000000000000000c0000000020000000000803003600000000000100100000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 451. -/
noncomputable def allowed451 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 451. -/
noncomputable def tree451 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [9]) (.split 68 (.pack [8]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [3]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 451. -/
theorem checked451 : checkParitySearch 8 (fun q => (rows451 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed451.contains) tree451 0xffedfb5ff7ffffffff03fe3ffffff7fe7ffeffbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 452. -/
noncomputable def rows452 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 452. -/
noncomputable def allowed452 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 452. -/
noncomputable def tree452 : ParitySearchTree := (.split 51 .done (.split 52 .done (.split 53 .done (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 93 (.pack [1]) (.split 94 (.pack [2]) (.split 95 (.pack [0]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 452. -/
theorem checked452 : checkParitySearch 8 (fun q => (rows452 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed452.contains) tree452 0xffedf83ff1ffffffffb7ff7fffffdffffffeff8fffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 453. -/
noncomputable def rows453 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 453. -/
noncomputable def allowed453 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 453. -/
noncomputable def tree453 : ParitySearchTree := (.split 51 .done (.split 52 .done (.split 53 .done (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 93 (.pack [1]) (.split 94 (.pack [2]) (.split 95 (.pack [0]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 453. -/
theorem checked453 : checkParitySearch 8 (fun q => (rows453 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed453.contains) tree453 0xffedf83ff1ffffffff6ffeffffffeffffffeff8fffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 454. -/
noncomputable def rows454 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 454. -/
noncomputable def allowed454 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 454. -/
noncomputable def tree454 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [8]) (.split 134 (.pack [7]) (.split 169 (.pack [9]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 454. -/
theorem checked454 : checkParitySearch 8 (fun q => (rows454 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed454.contains) tree454 0xffedf6dfefffffffff03fe3ffffff7e7fffeff7ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 455. -/
noncomputable def rows455 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000400000060000000000000000000002002400000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 455. -/
noncomputable def allowed455 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 455. -/
noncomputable def tree455 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [6]) (.split 17 (.pack [5]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 455. -/
theorem checked455 : checkParitySearch 8 (fun q => (rows455 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed455.contains) tree455 0xffededdfdfffffffff03fe3ffffff7ebfffefefffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 456. -/
noncomputable def rows456 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 456. -/
noncomputable def allowed456 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 456. -/
noncomputable def tree456 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [10]) (.split 68 (.pack [9]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 456. -/
theorem checked456 : checkParitySearch 8 (fun q => (rows456 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed456.contains) tree456 0xffeddbdfbfffffffff03fe3ffffff7f3fffefdfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 457. -/
noncomputable def rows457 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 457. -/
noncomputable def allowed457 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 457. -/
noncomputable def tree457 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [8]) (.split 134 (.pack [7]) (.split 169 (.pack [9]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 457. -/
theorem checked457 : checkParitySearch 8 (fun q => (rows457 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed457.contains) tree457 0xffedb7df7fffffffff03fe3ffffff73ffffefbfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 458. -/
noncomputable def rows458 : Nat := 0x8000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 458. -/
noncomputable def allowed458 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 458. -/
noncomputable def tree458 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 .done (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 458. -/
theorem checked458 : checkParitySearch 8 (fun q => (rows458 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed458.contains) tree458 0xffed7eb7fdfffffffffffb7febffe2fdfffcbfeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 459. -/
noncomputable def rows459 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 459. -/
noncomputable def allowed459 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 459. -/
noncomputable def tree459 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 459. -/
theorem checked459 : checkParitySearch 8 (fun q => (rows459 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed459.contains) tree459 0xffed6fdeffffffffff03fe3ffffff75ffffef7fffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 460. -/
noncomputable def rows460 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 460. -/
noncomputable def allowed460 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 460. -/
noncomputable def tree460 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 460. -/
theorem checked460 : checkParitySearch 8 (fun q => (rows460 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed460.contains) tree460 0xffecdfddffffffffff03fe3ffffff79ffffeeffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 461. -/
noncomputable def rows461 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200c0014000000010018002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000002000400c0018000080010010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180000000000000000000008009000000000000000000000004200c00d840008002000801a00980000082000200200000000000000000000402800140d80000400880080180108034408200000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 461. -/
noncomputable def allowed461 : List Nat := [0x10000000000000000,0x200000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 461. -/
noncomputable def tree461 : ParitySearchTree := (.split 34 (.pack [3]) (.split 37 (.pack [5]) (.split 50 (.pack [8]) (.split 52 (.pack [9]) (.split 53 (.pack [11]) (.split 62 (.pack [10]) (.split 64 .done (.split 77 (.pack [12]) (.split 91 (.pack [0]) (.split 92 (.pack [4]) (.split 104 (.pack [1]) (.split 138 (.pack [8]) (.split 140 (.pack [2]) (.split 154 (.pack [5]) (.split 155 (.pack [6]) (.split 165 .done (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 461. -/
theorem checked461 : checkParitySearch 8 (fun q => (rows461 >>> (256*q)) &&& (2^256-1)) 0x82 (allowed461.contains) tree461 0xffebffdfffffffffffba7fa7fe7fdcffcffeffffffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 462. -/
noncomputable def rows462 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000400000300000000000000000000002002400000000000000000000002800a00b402000000000880300260000104000010010000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 462. -/
noncomputable def allowed462 : List Nat := [0x1,0x20000000000000000,0x80000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 462. -/
noncomputable def tree462 : ParitySearchTree := (.split 0 .done (.split 12 (.pack [4]) (.split 34 (.pack [6]) (.split 40 (.pack [9]) (.split 61 (.pack [11]) (.split 62 (.pack [12]) (.split 65 .done (.split 76 (.pack [13]) (.split 77 (.pack [14]) (.split 87 (.pack [0]) (.split 91 .done (.split 129 (.pack [9]) (.split 138 (.pack [2]) (.split 140 (.pack [3]) (.split 141 (.pack [4]) (.split 143 (.pack [5]) (.split 153 (.pack [7]) (.split 155 (.pack [8]) (.split 167 (.pack [10]) (.split 169 .done (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 462. -/
theorem checked462 : checkParitySearch 8 (fun q => (rows462 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed462.contains) tree462 0xffebffbfffffffffff27f8bff3ffe7fe7ffdffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 463. -/
noncomputable def rows463 : Nat := 0xc0000000000000004000000800900000000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000002200a00b408000000000a001800b0000104000040040000000000000000000000a0000000040000000001002802d0000000000020020000000000000000000002800a00b4020000000008803002600001040000100100000000000000000000000000000000008000000c01200000000000000000040000000000000000000006006a000000002002002c0008020065000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 463. -/
noncomputable def allowed463 : List Nat := [0x1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 463. -/
noncomputable def tree463 : ParitySearchTree := (.split 0 .done (.split 48 (.pack [9]) (.split 50 (.pack [10]) (.split 53 (.pack [12]) (.split 54 (.pack [13]) (.split 65 (.pack [3]) (.split 75 (.pack [14]) (.split 90 (.pack [1]) (.split 91 (.pack [1]) (.split 93 (.pack [2]) (.split 105 (.pack [2]) (.split 117 (.pack [5]) (.split 153 (.pack [6]) (.split 155 (.pack [7]) (.split 157 (.pack [12]) (.split 158 (.pack [8]) (.split 169 (.pack [4]) (.split 170 (.pack [11]) (.zero 0)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 463. -/
theorem checked463 : checkParitySearch 8 (fun q => (rows463 >>> (256*q)) &&& (2^256-1)) 0x5 (allowed463.contains) tree463 0xffebffbffffffffffe23fafff3ffaffe7ffdfffffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 464. -/
noncomputable def rows464 : Nat := 0x400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000003000700600000000000000000000018018803f0000000000000000000000a0000000040000000001002802d00000000000200200000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 464. -/
noncomputable def allowed464 : List Nat := [0x1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 464. -/
noncomputable def tree464 : ParitySearchTree := (.split 0 .done (.split 1 (.pack [1]) (.split 2 (.pack [0]) (.split 3 (.pack [3]) (.split 4 (.pack [4]) (.split 5 (.pack [5]) (.split 15 (.pack [6]) (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 31 (.pack [8]) (.split 32 (.pack [9]) (.split 121 (.pack [7]) (.split 122 (.pack [7]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [8]) (.split 148 (.pack [10]) (.split 149 (.pack [10]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 464. -/
theorem checked464 : checkParitySearch 8 (fun q => (rows464 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed464.contains) tree464 0xffebffbfffffffedff23f8fff7ffeffe7ffdffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 465. -/
noncomputable def rows465 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000004200a00b40000000d000801a01840000104000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000004000800a00140000c0018018018002601000240000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 465. -/
noncomputable def allowed465 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x80000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 465. -/
noncomputable def tree465 : ParitySearchTree := (.split 22 (.pack [3]) (.split 25 (.pack [4]) (.split 40 (.pack [8]) (.split 49 (.pack [12]) (.split 50 (.pack [10]) (.split 53 (.pack [13]) (.split 67 (.pack [14]) (.split 68 (.pack [13]) (.split 79 .done (.split 80 .done (.split 91 .done (.split 92 (.pack [9]) (.split 106 .done (.split 107 (.pack [2]) (.split 126 (.pack [0]) (.split 128 (.pack [1]) (.split 141 (.pack [11]) (.split 143 (.pack [5]) (.split 155 (.pack [7]) (.split 170 (.pack [11]) (.zero 6)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 465. -/
theorem checked465 : checkParitySearch 8 (fun q => (rows465 >>> (256*q)) &&& (2^256-1)) 0x240 (allowed465.contains) tree465 0xffebffbfffffffdbfff7f9bffbffc7fe7ffdffffd7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 466. -/
noncomputable def rows466 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000a00c00000000800140100108025009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000100000050000000000000000000000800900000000000000000000006a00000004800000b800201a819d0000000000240200000000000000000000000000006002000800a00140090000000000030026010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 466. -/
noncomputable def allowed466 : List Nat := [0x20000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 466. -/
noncomputable def tree466 : ParitySearchTree := (.split 4 (.pack [2]) (.split 13 (.pack [3]) (.split 14 (.pack [4]) (.split 17 .done (.split 28 (.pack [5]) (.split 29 (.pack [6]) (.split 76 (.pack [10]) (.split 79 .done (.split 90 (.pack [8]) (.split 92 (.pack [8]) (.split 105 (.pack [11]) (.split 107 (.pack [8]) (.split 119 (.pack [1]) (.split 133 (.pack [7]) (.split 145 (.pack [9]) (.split 146 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 466. -/
theorem checked466 : checkParitySearch 8 (fun q => (rows466 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed466.contains) tree466 0xffebffbfffffffc9ffbbf97fffffdffe7ffdffffe7ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 467. -/
noncomputable def rows467 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000a000000040000009400001e81d500000000002002400000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000800000740000800840100028111025019400000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 467. -/
noncomputable def allowed467 : List Nat := [0x20000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 467. -/
noncomputable def tree467 : ParitySearchTree := (.split 2 (.pack [2]) (.split 5 (.pack [4]) (.split 17 .done (.split 60 (.pack [7]) (.split 62 (.pack [8]) (.split 64 (.pack [9]) (.split 66 (.pack [10]) (.split 67 (.pack [11]) (.split 68 (.pack [6]) (.split 75 (.pack [12]) (.split 77 (.pack [13]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 102 (.pack [2]) (.split 104 (.pack [1]) (.split 107 (.pack [0]) (.split 134 (.pack [5]) (.split 165 (.pack [9]) (.split 167 (.pack [9]) (.zero 3)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 467. -/
theorem checked467 : checkParitySearch 8 (fun q => (rows467 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed467.contains) tree467 0xffebffbfffffffc9ff9ff93fffffd7fe7ffdffffe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 468. -/
noncomputable def rows468 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000a0000000040000000001002802d00000000000200200000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 468. -/
noncomputable def allowed468 : List Nat := [0x1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 468. -/
noncomputable def tree468 : ParitySearchTree := (.split 0 .done (.split 1 (.pack [1]) (.split 2 (.pack [0]) (.split 3 (.pack [3]) (.split 4 (.pack [4]) (.split 5 (.pack [5]) (.split 15 (.pack [6]) (.split 16 (.pack [7]) (.split 17 (.pack [8]) (.split 132 (.pack [10]) (.split 133 (.pack [11]) (.split 134 (.pack [9]) (.zero 2)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 468. -/
theorem checked468 : checkParitySearch 8 (fun q => (rows468 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed468.contains) tree468 0xffebfdfffbffffffff03f8fff3ffeffcfffdffdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 469. -/
noncomputable def rows469 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000006000400800140140000000000000030034000402400000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000000040000008009001c01f8000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 469. -/
noncomputable def allowed469 : List Nat := [0x10000000000000,0x20000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 469. -/
noncomputable def tree469 : ParitySearchTree := (.split 5 (.pack [1]) (.split 51 (.pack [4]) (.split 52 .done (.split 53 .done (.split 54 (.pack [5]) (.split 55 (.pack [6]) (.split 56 (.pack [7]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 80 (.pack [2]) (.split 83 (.pack [10]) (.split 95 (.pack [2]) (.split 122 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 469. -/
theorem checked469 : checkParitySearch 8 (fun q => (rows469 >>> (256*q)) &&& (2^256-1)) 0x5 (allowed469.contains) tree469 0xffebfcdff9ffffffffdbf97ff3ffdffffffdffcfffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 470. -/
noncomputable def rows470 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000a0000000040000000001002802d00000000000200200000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 470. -/
noncomputable def allowed470 : List Nat := [0x1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 470. -/
noncomputable def tree470 : ParitySearchTree := (.split 0 .done (.split 1 (.pack [1]) (.split 2 (.pack [0]) (.split 3 (.pack [3]) (.split 4 (.pack [4]) (.split 5 (.pack [5]) (.split 15 (.pack [6]) (.split 16 (.pack [7]) (.split 17 (.pack [8]) (.split 132 (.pack [10]) (.split 133 (.pack [11]) (.split 134 (.pack [9]) (.zero 2)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 470. -/
theorem checked470 : checkParitySearch 8 (fun q => (rows470 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed470.contains) tree470 0xffebfb3ff7ffffffff03f8fff3ffeffffffdffbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 471. -/
noncomputable def rows471 : Nat := 0x8000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 471. -/
noncomputable def allowed471 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 471. -/
noncomputable def tree471 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 .done (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 471. -/
theorem checked471 : checkParitySearch 8 (fun q => (rows471 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed471.contains) tree471 0xffebbebbfdfffffffffffb7febffe1fdfffcdfeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 472. -/
noncomputable def rows472 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 472. -/
noncomputable def allowed472 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 472. -/
noncomputable def tree472 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [4]) (.split 17 (.pack [5]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [6]) (.split 134 (.pack [6]) (.split 169 (.pack [7]) (.split 170 (.pack [2]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 472. -/
theorem checked472 : checkParitySearch 8 (fun q => (rows472 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed472.contains) tree472 0xffe9ffdfffffffffff0afe97fd7ff5ffdffefffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 473. -/
noncomputable def rows473 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000400800140140000000180000030034000402400000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000400800940180180000080080010000011400201200000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000004000003000000000000000000000020024000000000000000000000060000000010000000000001801b0000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 473. -/
noncomputable def allowed473 : List Nat := [0x20000000000000000000,0x100000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 473. -/
noncomputable def tree473 : ParitySearchTree := (.split 34 (.pack [3]) (.split 37 (.pack [6]) (.split 46 (.pack [7]) (.split 62 (.pack [11]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 76 (.pack [12]) (.split 77 .done (.split 103 (.pack [5]) (.split 104 .done (.split 138 (.pack [1]) (.split 140 (.pack [2]) (.split 150 (.pack [10]) (.split 152 (.pack [4]) (.split 167 (.pack [9]) (.split 178 (.pack [5]) (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 473. -/
theorem checked473 : checkParitySearch 8 (fun q => (rows473 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed473.contains) tree473 0xffe9ffdffffffff6ff3efed7ff7ffdffdffefffffcff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 474. -/
noncomputable def rows474 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f0000000000000000000002000800ac09800000000a001800b0010106012040040000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 474. -/
noncomputable def allowed474 : List Nat := [0x1,0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 474. -/
noncomputable def tree474 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 (.pack [1]) (.split 3 (.pack [3]) (.split 4 (.pack [0]) (.split 5 (.pack [4]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [8]) (.zero 2)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 474. -/
theorem checked474 : checkParitySearch 8 (fun q => (rows474 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed474.contains) tree474 0xffe9ff9fffffffffff03fabfebffdffefffcfffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 475. -/
noncomputable def rows475 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000002000800a0014000000018000003002601000240000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000080000010002003803f0000000000040040000000000000000000000000004005000400a0018004800000000002000c02c

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 475. -/
noncomputable def allowed475 : List Nat := [0x10000000000000000,0x20000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 475. -/
noncomputable def tree475 : ParitySearchTree := (.split 2 (.pack [0]) (.split 14 (.pack [2]) (.split 60 (.pack [5]) (.split 61 (.pack [6]) (.split 62 (.pack [7]) (.split 63 (.pack [8]) (.split 64 .done (.split 65 .done (.split 75 (.pack [9]) (.split 76 (.pack [10]) (.split 77 (.pack [11]) (.split 89 (.pack [11]) (.split 104 (.pack [3]) (.split 131 (.pack [4]) (.zero 1)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 475. -/
theorem checked475 : checkParitySearch 8 (fun q => (rows475 >>> (256*q)) &&& (2^256-1)) 0xa (allowed475.contains) tree475 0xffe9ff9fffffffedffb3fbbfeffffffefffcffffcfffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 476. -/
noncomputable def rows476 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000004002000400c0018000080000010010002c00800120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00200000000000000000040040000000000000000000006000a00000000800c000400a01a00120000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 476. -/
noncomputable def allowed476 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 476. -/
noncomputable def tree476 : ParitySearchTree := (.split 2 (.pack [2]) (.split 49 (.pack [8]) (.split 52 .done (.split 65 .done (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 77 (.pack [11]) (.split 79 (.pack [0]) (.split 90 (.pack [0]) (.split 106 (.pack [4]) (.split 107 (.pack [3]) (.split 119 (.pack [6]) (.split 153 .done (.split 155 (.pack [7]) (.split 169 .done (.split 170 (.pack [5]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 476. -/
theorem checked476 : checkParitySearch 8 (fun q => (rows476 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed476.contains) tree476 0xffe9fef7fd7ffffffffffb7febffe7fdaffcffebfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 477. -/
noncomputable def rows477 : Nat := 0x8000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000800000d40800800c801200a818100d034400004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 477. -/
noncomputable def allowed477 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 477. -/
noncomputable def tree477 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 .done (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 477. -/
theorem checked477 : checkParitySearch 8 (fun q => (rows477 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed477.contains) tree477 0xffe9febffdffffffffdbfb3febffeffdfffcffefffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 478. -/
noncomputable def rows478 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000080000010002003803f000000000004004000000000000000000000600000000500020080018000804800000000002802c

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 478. -/
noncomputable def allowed478 : List Nat := [0x20000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 478. -/
noncomputable def tree478 : ParitySearchTree := (.split 2 (.pack [0]) (.split 14 (.pack [2]) (.split 60 (.pack [6]) (.split 61 (.pack [7]) (.split 62 (.pack [8]) (.split 63 (.pack [0]) (.split 64 (.pack [5]) (.split 65 .done (.split 75 (.pack [9]) (.split 76 (.pack [10]) (.split 77 (.pack [11]) (.split 89 (.pack [11]) (.split 104 (.pack [3]) (.split 131 (.pack [4]) (.zero 1)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 478. -/
theorem checked478 : checkParitySearch 8 (fun q => (rows478 >>> (256*q)) &&& (2^256-1)) 0xa (allowed478.contains) tree478 0xffe9febffdffffffff93fbbfebfffffdfffcffefffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 479. -/
noncomputable def rows479 : Nat := 0x8000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 479. -/
noncomputable def allowed479 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 479. -/
noncomputable def tree479 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 .done (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 479. -/
theorem checked479 : checkParitySearch 8 (fun q => (rows479 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed479.contains) tree479 0xffe9febffdfffffffdbfff7febff67fdfffcffeffffd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 480. -/
noncomputable def rows480 : Nat := 0x8000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 480. -/
noncomputable def allowed480 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 480. -/
noncomputable def tree480 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 .done (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 480. -/
theorem checked480 : checkParitySearch 8 (fun q => (rows480 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed480.contains) tree480 0xffe9febffdffffedffdffb7fefffe7fdfffcffefcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 481. -/
noncomputable def rows481 : Nat := 0x8000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 481. -/
noncomputable def allowed481 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 481. -/
noncomputable def tree481 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 .done (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 481. -/
theorem checked481 : checkParitySearch 8 (fun q => (rows481 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed481.contains) tree481 0xffe9febffdffffb7ff7ffb7ffbffe7fdfffcffefe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 482. -/
noncomputable def rows482 : Nat := 0x8000000c00000000000000000000040048000000000000000000000000000004800000d8000000048000009008200900820000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 482. -/
noncomputable def allowed482 : List Nat := [0x10000000000000,0x20000000000000000,0x200000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 482. -/
noncomputable def tree482 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [3]) (.split 38 (.pack [6]) (.split 40 (.pack [7]) (.split 41 (.pack [8]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 .done (.split 92 (.pack [0]) (.split 126 (.pack [6]) (.split 128 (.pack [1]) (.split 142 (.pack [3]) (.split 143 (.pack [4]) (.split 153 .done (.split 169 .done (.split 170 (.pack [9]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 482. -/
theorem checked482 : checkParitySearch 8 (fun q => (rows482 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed482.contains) tree482 0xffe9f7bfedfffffffffffb7febffe7e5fffcff6ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 483. -/
noncomputable def rows483 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 483. -/
noncomputable def allowed483 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 483. -/
noncomputable def tree483 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 483. -/
theorem checked483 : checkParitySearch 8 (fun q => (rows483 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed483.contains) tree483 0xffe97fd7ffffffffff03fe3ffffff2fffffebffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 484. -/
noncomputable def rows484 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000c06800180140000000d800001b0180004c024000000000000000000000000000404000900c001b000040008008008201840820104000000000000000000000000000000001000000180000000000000000000008009000000000000000000000004800800d0014002848004009008a00000a2020004800000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 484. -/
noncomputable def allowed484 : List Nat := [0x400000000,0x4000000000000,0x40000000000000000000000000000000000,0x80000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 484. -/
noncomputable def tree484 : ParitySearchTree := (.split 34 .done (.split 37 (.pack [8]) (.split 46 (.pack [9]) (.split 47 (.pack [10]) (.split 50 .done (.split 67 (.pack [11]) (.split 68 (.pack [12]) (.split 76 (.pack [0]) (.split 77 (.pack [1]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 103 (.pack [2]) (.split 104 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [3]) (.split 138 .done (.split 140 (.pack [5]) (.split 151 .done (.split 152 (.pack [6]) (.split 167 (.pack [4]) (.split 169 (.pack [8]) (.split 170 (.pack [13]) (.split 178 (.pack [15]) (.split 179 (.pack [14]) (.zero 7)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 484. -/
theorem checked484 : checkParitySearch 8 (fun q => (rows484 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed484.contains) tree484 0xffe97fbbff77ff7fffffffffffffcaffcffe7ff9fffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 485. -/
noncomputable def rows485 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000001000000c000000000000000000000080090000000000000000000000004200c00d8200000000004014016000000820001001200000000000000000000060000000010000000000001801b0000000000008009000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000040000006009000000000000000000200000000000000000000800600cc00000008001001401000100328000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 485. -/
noncomputable def allowed485 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 485. -/
noncomputable def tree485 : ParitySearchTree := (.split 2 .done (.split 47 (.pack [10]) (.split 49 (.pack [11]) (.split 52 (.pack [13]) (.split 53 (.pack [14]) (.split 64 (.pack [4]) (.split 80 (.pack [2]) (.split 90 (.pack [0]) (.split 92 (.pack [0]) (.split 104 (.pack [3]) (.split 119 (.pack [6]) (.split 150 (.pack [12]) (.split 151 (.pack [7]) (.split 154 (.pack [8]) (.split 155 (.pack [9]) (.split 165 (.pack [5]) (.split 166 (.pack [11]) (.split 179 (.pack [15]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 485. -/
theorem checked485 : checkParitySearch 8 (fun q => (rows485 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed485.contains) tree485 0xffe7ffdfffffffffff157f57fd7ff2ffaffefffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 486. -/
noncomputable def rows486 : Nat := (Nat.lor 0x100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000034006000c24000002200200280290040009000120104000000000000000000000060000000080000000002001801b0000000000040040000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000000800000600120000000000000000004000000000000000000000020054006000c1000200640200100141020004800008 (Nat.shiftLeft 0x2800000000000000200000040048000000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000005000000000000000400000080090000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 486. -/
noncomputable def allowed486 : List Nat := [0x80000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 486. -/
noncomputable def tree486 : ParitySearchTree := (.split 2 (.pack [3]) (.split 8 (.pack [2]) (.split 17 (.pack [7]) (.split 20 (.pack [8]) (.split 36 (.pack [9]) (.split 39 (.pack [10]) (.split 54 (.pack [14]) (.split 64 (.pack [3]) (.split 67 (.pack [16]) (.split 69 (.pack [17]) (.split 79 .done (.split 81 (.pack [1]) (.split 93 (.pack [0]) (.split 105 (.pack [0]) (.split 109 (.pack [18]) (.split 134 (.pack [12]) (.split 137 (.pack [13]) (.split 142 (.pack [5]) (.split 143 (.pack [6]) (.split 157 (.pack [11]) (.split 158 (.pack [16]) (.split 170 .done (.split 172 (.pack [15]) (.split 173 (.pack [18]) (.zero 4)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 486. -/
theorem checked486 : checkParitySearch 8 (fun q => (rows486 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed486.contains) tree486 0xffe7ff7ffffffffffeb3f67febffbffd7ffbfffffffcc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 487. -/
noncomputable def rows487 : Nat := 0x50000000000000004000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000004000600c000000004000c0080088013009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002002000c00c0000080080010002016000804800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000006c00000d80000000000000000000036030c000000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 487. -/
noncomputable def allowed487 : List Nat := [0x8000000000000000,0x80000000000000000000,0x40000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 487. -/
noncomputable def tree487 : ParitySearchTree := (.split 36 (.pack [2]) (.split 39 (.pack [5]) (.split 48 (.pack [6]) (.split 49 (.pack [7]) (.split 52 (.pack [10]) (.split 63 .done (.split 67 (.pack [10]) (.split 79 .done (.split 90 .done (.split 91 (.pack [4]) (.split 106 (.pack [0]) (.split 142 (.pack [1]) (.split 143 (.pack [9]) (.split 153 (.pack [2]) (.split 154 (.pack [3]) (.split 170 .done (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 487. -/
theorem checked487 : checkParitySearch 8 (fun q => (rows487 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed487.contains) tree487 0xffe7ff7ffffffffdbfdff4ffeb7feffd7ffbfffff9ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 488. -/
noncomputable def rows488 : Nat := (Nat.lor 0x300000000000000010000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000040054006000c2000000040480148141020004800010 (Nat.shiftLeft 0x180000000000000040000008009000000000000000000000000000000000000006000000000000000200000040048000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 488. -/
noncomputable def allowed488 : List Nat := [0x80000000000000000000,0x40000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 488. -/
noncomputable def tree488 : ParitySearchTree := (.split 4 (.pack [4]) (.split 23 (.pack [5]) (.split 26 (.pack [8]) (.split 41 (.pack [12]) (.split 48 (.pack [13]) (.split 54 (.pack [15]) (.split 56 (.pack [14]) (.split 63 (.pack [16]) (.split 66 (.pack [16]) (.split 68 (.pack [17]) (.split 79 .done (.split 82 (.pack [1]) (.split 90 .done (.split 121 (.pack [9]) (.split 126 (.pack [2]) (.split 127 (.pack [3]) (.split 141 (.pack [6]) (.split 142 (.pack [7]) (.split 154 (.pack [10]) (.split 156 (.pack [11]) (.split 158 (.pack [12]) (.split 170 (.pack [16]) (.zero 0)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 488. -/
theorem checked488 : checkParitySearch 8 (fun q => (rows488 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed488.contains) tree488 0xffe7ff7fffffffedffb3f47feffffffd7ffbffffcfffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 489. -/
noncomputable def rows489 : Nat := 0x50000000000000004000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000004000600c000000004000c0080088013009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002002000c00c000008008001000201600080480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000040000014000000000000000000000200240000000000000000000000060066080010020000004c08801e8053000040040029

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 489. -/
noncomputable def allowed489 : List Nat := [0x8000000000000000,0x80000000000000000000,0x40000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 489. -/
noncomputable def tree489 : ParitySearchTree := (.split 36 (.pack [2]) (.split 39 (.pack [5]) (.split 48 (.pack [6]) (.split 49 (.pack [7]) (.split 52 (.pack [10]) (.split 63 .done (.split 67 (.pack [10]) (.split 79 .done (.split 90 .done (.split 91 (.pack [4]) (.split 106 (.pack [0]) (.split 142 (.pack [1]) (.split 143 (.pack [9]) (.split 153 (.pack [2]) (.split 154 (.pack [3]) (.split 170 .done (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 489. -/
theorem checked489 : checkParitySearch 8 (fun q => (rows489 >>> (256*q)) &&& (2^256-1)) 0x101 (allowed489.contains) tree489 0xffe7ff7fffffffb7ff5bf4fffbffeffd7ffbffffe7ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 490. -/
noncomputable def rows490 : Nat := 0x600000000000000020000004004800000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000004000600c000000004000c0080088013009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002002000c00c000008008001000201600080480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000060040004006000c0120000000000030016020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 490. -/
noncomputable def allowed490 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 490. -/
noncomputable def tree490 : ParitySearchTree := (.split 36 (.pack [2]) (.split 39 (.pack [5]) (.split 48 (.pack [6]) (.split 49 (.pack [7]) (.split 52 (.pack [10]) (.split 63 (.pack [11]) (.split 67 (.pack [10]) (.split 79 .done (.split 90 (.pack [0]) (.split 91 (.pack [4]) (.split 106 (.pack [0]) (.split 142 (.pack [1]) (.split 143 (.pack [9]) (.split 153 (.pack [2]) (.split 154 (.pack [3]) (.split 170 (.pack [11]) (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 490. -/
theorem checked490 : checkParitySearch 8 (fun q => (rows490 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed490.contains) tree490 0xffe7ff7fffffffa5ff7bf4ffffffeffd7ffbffffd7ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 491. -/
noncomputable def rows491 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000001000000500000000000000000000008009000000000000000000000006000000020000004c00001d81e300000000001001200000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000400000ac00004004400800180a1013029800000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 491. -/
noncomputable def allowed491 : List Nat := [0x10000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 491. -/
noncomputable def tree491 : ParitySearchTree := (.split 1 (.pack [1]) (.split 4 (.pack [4]) (.split 16 .done (.split 60 (.pack [7]) (.split 61 (.pack [8]) (.split 65 (.pack [9]) (.split 66 (.pack [10]) (.split 67 (.pack [6]) (.split 68 (.pack [11]) (.split 75 (.pack [12]) (.split 76 (.pack [13]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 102 (.pack [1]) (.split 103 (.pack [2]) (.split 106 (.pack [0]) (.split 133 (.pack [5]) (.split 165 (.pack [9]) (.split 166 (.pack [9]) (.zero 3)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 491. -/
theorem checked491 : checkParitySearch 8 (fun q => (rows491 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed491.contains) tree491 0xffe7ff7fffffffa5ff5ff4bfffffe7fd7ffbffffd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 492. -/
noncomputable def rows492 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000004200400cc00c000048004009008a00500980480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000004004400c00d800004004c00800080830000082000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000002004000800c0018000040000008008001a00800120000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 492. -/
noncomputable def allowed492 : List Nat := [0x8000000000000000,0x80000000000000000000,0x40000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 492. -/
noncomputable def tree492 : ParitySearchTree := (.split 21 (.pack [3]) (.split 27 (.pack [7]) (.split 48 (.pack [13]) (.split 49 (.pack [14]) (.split 55 (.pack [15]) (.split 63 .done (.split 79 .done (.split 90 .done (.split 91 (.pack [10]) (.split 94 (.pack [4]) (.split 106 (.pack [2]) (.split 127 (.pack [0]) (.split 128 (.pack [1]) (.split 130 (.pack [12]) (.split 131 (.pack [11]) (.split 142 (.pack [5]) (.split 143 (.pack [6]) (.split 154 (.pack [9]) (.split 158 (.pack [12]) (.split 170 .done (.zero 8)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 492. -/
theorem checked492 : checkParitySearch 8 (fun q => (rows492 >>> (256*q)) &&& (2^256-1)) 0x500 (allowed492.contains) tree492 0xffe7fe5ffdffffffffdbf4ffebffeffe7ffbffefffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 493. -/
noncomputable def rows493 : Nat := 0x4000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000004000000200180140000040000008029022004c02400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000060000000080000000002001801b00000000000400400000000000000000000000000000000800000280120000000000000000004000000000000000000000000005000000002000000000480140168000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 493. -/
noncomputable def allowed493 : List Nat := [0x40000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 493. -/
noncomputable def tree493 : ParitySearchTree := (.split 10 (.pack [1]) (.split 13 (.pack [8]) (.split 22 (.pack [3]) (.split 23 (.pack [4]) (.split 26 (.pack [7]) (.split 37 (.pack [12]) (.split 41 (.pack [10]) (.split 48 (.pack [11]) (.split 51 (.pack [0]) (.split 53 (.pack [0]) (.split 63 (.pack [2]) (.split 90 .done (.split 114 (.pack [7]) (.split 116 (.pack [5]) (.split 127 (.pack [1]) (.split 128 (.pack [9]) (.split 141 (.pack [5]) (.split 170 .done (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 493. -/
theorem checked493 : checkParitySearch 8 (fun q => (rows493 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed493.contains) tree493 0xffe7fd3ffbffffffff93f47febfffffffffbffdfffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 494. -/
noncomputable def rows494 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000000200a000c000040008008008003a029004800000000000000000000000000000001000000500000000000000000000008009000000000000000000000000040002008001401404000c008008801300b0004024000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000080000060012000000000000000000400000000000000000000006005000000001000200600200108168000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 494. -/
noncomputable def allowed494 : List Nat := [0x8000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 494. -/
noncomputable def tree494 : ParitySearchTree := (.split 3 (.pack [2]) (.split 51 (.pack [5]) (.split 53 (.pack [5]) (.split 54 (.pack [8]) (.split 56 (.pack [9]) (.split 63 .done (.split 68 (.pack [10]) (.split 81 (.pack [1]) (.split 93 (.pack [3]) (.split 94 (.pack [7]) (.split 105 (.pack [3]) (.split 120 (.pack [4]) (.split 156 (.pack [7]) (.split 158 (.pack [7]) (.split 169 (.pack [6]) (.split 170 .done (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 494. -/
theorem checked494 : checkParitySearch 8 (fun q => (rows494 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed494.contains) tree494 0xffe7fd3ffbfffffffefbf6ffebffaffffffbffdffffc9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 495. -/
noncomputable def rows495 : Nat := (Nat.lor 0x50000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000200a000c000040008008008003a02900480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000036000006c000000000000000000001b018600000000000000000000000000000008000000c000000000000000000000400480000000000000000000000040002008001401404000c008008801300b000402400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000000000400000300090000000000000000002000000000000000000000000005000000002000000000480140168000000000010 (Nat.shiftLeft 0x6000000000000000200000040048000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 495. -/
noncomputable def allowed495 : List Nat := [0x40000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 495. -/
noncomputable def tree495 : ParitySearchTree := (.split 10 (.pack [2]) (.split 13 (.pack [8]) (.split 22 (.pack [4]) (.split 36 (.pack [9]) (.split 37 (.pack [13]) (.split 39 (.pack [11]) (.split 48 (.pack [12]) (.split 49 (.pack [13]) (.split 52 (.pack [14]) (.split 63 (.pack [16]) (.split 67 (.pack [15]) (.split 79 (.pack [0]) (.split 90 .done (.split 91 (.pack [10]) (.split 106 (.pack [3]) (.split 114 (.pack [7]) (.split 116 (.pack [5]) (.split 126 (.pack [1]) (.split 128 (.pack [9]) (.split 143 (.pack [14]) (.split 153 (.pack [9]) (.split 170 (.pack [16]) (.zero 6)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 495. -/
theorem checked495 : checkParitySearch 8 (fun q => (rows495 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed495.contains) tree495 0xffe7fd3ffbffffedfffbf4ffefffeffffffbffdfcfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 496. -/
noncomputable def rows496 : Nat := (Nat.lor 0x30000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000040018006006c2000000000480140148000020800010 (Nat.shiftLeft 0x18000000000000004000000800900000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 496. -/
noncomputable def allowed496 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 496. -/
noncomputable def tree496 : ParitySearchTree := (.split 4 (.pack [5]) (.split 23 (.pack [6]) (.split 29 (.pack [9]) (.split 51 .done (.split 54 (.pack [13]) (.split 56 (.pack [14]) (.split 66 (.pack [15]) (.split 68 (.pack [16]) (.split 79 .done (.split 82 (.pack [1]) (.split 121 (.pack [10]) (.split 126 (.pack [2]) (.split 127 (.pack [3]) (.split 129 (.pack [12]) (.split 130 (.pack [4]) (.split 141 (.pack [7]) (.split 142 (.pack [8]) (.split 155 .done (.split 156 (.pack [11]) (.split 170 .done (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 496. -/
theorem checked496 : checkParitySearch 8 (fun q => (rows496 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed496.contains) tree496 0xffe7fbfff7ffffffffb7f43febfff7fcfffbffbfffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 497. -/
noncomputable def rows497 : Nat := (Nat.lor 0x30000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000040018006006c2000000000480140148000020800010 (Nat.shiftLeft 0x18000000000000004000000800900000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 497. -/
noncomputable def allowed497 : List Nat := [0x80000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 497. -/
noncomputable def tree497 : ParitySearchTree := (.split 4 (.pack [4]) (.split 23 (.pack [5]) (.split 29 (.pack [8]) (.split 51 (.pack [12]) (.split 54 (.pack [13]) (.split 56 (.pack [14]) (.split 66 (.pack [15]) (.split 68 (.pack [16]) (.split 79 .done (.split 82 (.pack [1]) (.split 121 (.pack [9]) (.split 126 (.pack [2]) (.split 127 (.pack [3]) (.split 129 (.pack [11]) (.split 130 (.pack [10]) (.split 141 (.pack [6]) (.split 142 (.pack [7]) (.split 155 (.pack [12]) (.split 156 (.pack [10]) (.split 170 .done (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 497. -/
theorem checked497 : checkParitySearch 8 (fun q => (rows497 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed497.contains) tree497 0xffe7fbfff7ffffffff93f47febfffffcfffbffbfffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 498. -/
noncomputable def rows498 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002012000c06c00000804800100820860208208000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c0000400000080080032020004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000004000000600000000000000000000020024

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 498. -/
noncomputable def allowed498 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 498. -/
noncomputable def tree498 : ParitySearchTree := (.split 36 (.pack [4]) (.split 37 (.pack [5]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 .done (.split 67 (.pack [11]) (.split 79 .done (.split 91 (.pack [6]) (.split 106 (.pack [0]) (.split 141 (.pack [1]) (.split 142 (.pack [2]) (.split 153 (.pack [4]) (.split 155 .done (.split 169 (.pack [3]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 498. -/
theorem checked498 : checkParitySearch 8 (fun q => (rows498 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed498.contains) tree498 0xffe7fbfff7ffffffff6ff5bfebffc7fcfffbffbfffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 499. -/
noncomputable def rows499 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002012000c06c00000804800100820860208208000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c0000400000080080032020004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 499. -/
noncomputable def allowed499 : List Nat := [0x80000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 499. -/
noncomputable def tree499 : ParitySearchTree := (.split 36 (.pack [4]) (.split 37 (.pack [5]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 (.pack [11]) (.split 67 (.pack [12]) (.split 79 .done (.split 91 (.pack [6]) (.split 106 (.pack [0]) (.split 141 (.pack [1]) (.split 142 (.pack [2]) (.split 153 (.pack [4]) (.split 155 (.pack [11]) (.split 169 (.pack [3]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 499. -/
theorem checked499 : checkParitySearch 8 (fun q => (rows499 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed499.contains) tree499 0xffe7fbfff7fffffffefbf6ffebffaffcfffbffbffffc9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 500. -/
noncomputable def rows500 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c0000400000080080032020004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c000000000000000000000080090000000000000000000004400a006c0000400040000098021009020800000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 500. -/
noncomputable def allowed500 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 500. -/
noncomputable def tree500 : ParitySearchTree := (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 .done (.split 67 (.pack [11]) (.split 79 .done (.split 91 (.pack [0]) (.split 106 (.pack [1]) (.split 141 (.pack [2]) (.split 142 (.pack [3]) (.split 153 (.pack [5]) (.split 155 .done (.split 169 (.pack [4]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 500. -/
theorem checked500 : checkParitySearch 8 (fun q => (rows500 >>> (256*q)) &&& (2^256-1)) 0x401 (allowed500.contains) tree500 0xffe7fbfff7fffffffedff6bfebffa7fcfffbffbffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 501. -/
noncomputable def rows501 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c000040000008008003202000480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000024006006c0000200240080000061000020800000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 501. -/
noncomputable def allowed501 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 501. -/
noncomputable def tree501 : ParitySearchTree := (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 .done (.split 67 (.pack [11]) (.split 79 .done (.split 91 (.pack [0]) (.split 106 (.pack [1]) (.split 141 (.pack [2]) (.split 142 (.pack [3]) (.split 153 (.pack [5]) (.split 155 .done (.split 169 (.pack [4]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 501. -/
theorem checked501 : checkParitySearch 8 (fun q => (rows501 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed501.contains) tree501 0xffe7fbfff7fffffffb7ffcbfebfee7fcfffbffbffffe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 502. -/
noncomputable def rows502 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000002012000c06c000008048001008208602082080000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 502. -/
noncomputable def allowed502 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 502. -/
noncomputable def tree502 : ParitySearchTree := (.split 36 (.pack [3]) (.split 37 (.pack [4]) (.split 39 (.pack [6]) (.split 40 (.pack [7]) (.split 49 (.pack [8]) (.split 51 (.pack [10]) (.split 67 (.pack [12]) (.split 79 .done (.split 91 (.pack [5]) (.split 106 (.pack [0]) (.split 141 (.pack [1]) (.split 142 (.pack [2]) (.split 153 (.pack [3]) (.split 155 (.pack [10]) (.split 169 (.pack [11]) (.split 170 (.pack [11]) (.zero 9)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 502. -/
theorem checked502 : checkParitySearch 8 (fun q => (rows502 >>> (256*q)) &&& (2^256-1)) 0x200 (allowed502.contains) tree502 0xffe7fbfff7ffffedfffbf4ffefffeffcfffbffbfcfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 503. -/
noncomputable def rows503 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c0000400000080080032020004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c000000000000000000000080090000000000000000000004400a006c0000400040000098021009020800000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 503. -/
noncomputable def allowed503 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 503. -/
noncomputable def tree503 : ParitySearchTree := (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 .done (.split 67 (.pack [11]) (.split 79 .done (.split 91 (.pack [0]) (.split 106 (.pack [1]) (.split 141 (.pack [2]) (.split 142 (.pack [3]) (.split 153 (.pack [5]) (.split 155 .done (.split 169 (.pack [4]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 503. -/
theorem checked503 : checkParitySearch 8 (fun q => (rows503 >>> (256*q)) &&& (2^256-1)) 0x401 (allowed503.contains) tree503 0xffe7fbfff7ffffedffdff4bfefffe7fcfffbffbfcffff 0 1 = true := by decide +kernel

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

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
/-- Packed parity neighborhoods for affine fiber 504. -/
noncomputable def rows504 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000006000a0060000000040008008008000a01b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000020010002006000c000040000008008003202000480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000024006006c0000200240080000061000020800000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 504. -/
noncomputable def allowed504 : List Nat := [0x8000000000000,0x80000000000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 504. -/
noncomputable def tree504 : ParitySearchTree := (.split 36 (.pack [5]) (.split 37 (.pack [6]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 .done (.split 67 (.pack [11]) (.split 79 .done (.split 91 (.pack [0]) (.split 106 (.pack [1]) (.split 141 (.pack [2]) (.split 142 (.pack [3]) (.split 153 (.pack [5]) (.split 155 .done (.split 169 (.pack [4]) (.split 170 .done (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 504. -/
theorem checked504 : checkParitySearch 8 (fun q => (rows504 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed504.contains) tree504 0xffe7fbfff7ffffb7ff7ff4bffbffe7fcfffbffbfe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 505. -/
noncomputable def rows505 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000022000000c000000048000009008203c03b800000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000060008004000c00c0000000000000030032000804800000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000020000004004801c01f8000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 505. -/
noncomputable def allowed505 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 505. -/
noncomputable def tree505 : ParitySearchTree := (.split 4 (.pack [1]) (.split 51 (.pack [5]) (.split 52 (.pack [2]) (.split 53 (.pack [2]) (.split 54 (.pack [6]) (.split 55 (.pack [7]) (.split 56 (.pack [8]) (.split 66 (.pack [9]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 79 .done (.split 82 (.pack [10]) (.split 94 (.pack [4]) (.split 121 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 505. -/
theorem checked505 : checkParitySearch 8 (fun q => (rows505 >>> (256*q)) &&& (2^256-1)) 0x11 (allowed505.contains) tree505 0xffe7fadff5ffffffffdbf4ffebffeffffffbffafffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 506. -/
noncomputable def rows506 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 506. -/
noncomputable def allowed506 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 506. -/
noncomputable def tree506 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [4]) (.split 17 (.pack [5]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [6]) (.split 134 (.pack [6]) (.split 169 (.pack [7]) (.split 170 (.pack [2]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 506. -/
theorem checked506 : checkParitySearch 8 (fun q => (rows506 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed506.contains) tree506 0xffe5ffdfffffffffff11ff27fe7ff3ffbffefffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 507. -/
noncomputable def rows507 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f000000000000000000000400040074058000000011002800d001020a012020020000000000000000000000000000000004000000600900000000000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 507. -/
noncomputable def allowed507 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 507. -/
noncomputable def tree507 : ParitySearchTree := (.split 0 (.pack [1]) (.split 1 .done (.split 2 (.pack [1]) (.split 3 (.pack [3]) (.split 4 (.pack [4]) (.split 5 (.pack [0]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [8]) (.zero 2)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 507. -/
theorem checked507 : checkParitySearch 8 (fun q => (rows507 >>> (256*q)) &&& (2^256-1)) 0x6 (allowed507.contains) tree507 0xffe5ff5fffffffffff03f73ff3ffeffdfffafffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 508. -/
noncomputable def rows508 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000040004006000c00000001800000300160200048000000000000000000000000004000400740180000080100010032001020a012000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000040000008001003803f000000000002002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 508. -/
noncomputable def allowed508 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 508. -/
noncomputable def tree508 : ParitySearchTree := (.split 1 .done (.split 13 (.pack [1]) (.split 60 (.pack [5]) (.split 61 (.pack [6]) (.split 62 (.pack [7]) (.split 63 (.pack [8]) (.split 64 (.pack [3]) (.split 65 (.pack [3]) (.split 75 (.pack [9]) (.split 76 (.pack [10]) (.split 77 (.pack [11]) (.split 88 (.pack [10]) (.split 103 (.pack [2]) (.split 130 (.pack [4]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 508. -/
theorem checked508 : checkParitySearch 8 (fun q => (rows508 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed508.contains) tree508 0xffe5ff5fffffffedff6bf7bff7fffffdfffaffffcfffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 509. -/
noncomputable def rows509 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000180000000000000008000001001200000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000040000008001003803f000000000002002000000000000000000000600000000300020040018000804800000000001801a

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 509. -/
noncomputable def allowed509 : List Nat := [0x2,0x8000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 509. -/
noncomputable def tree509 : ParitySearchTree := (.split 1 .done (.split 13 (.pack [2]) (.split 60 (.pack [5]) (.split 61 (.pack [6]) (.split 62 (.pack [7]) (.split 63 .done (.split 64 (.pack [0]) (.split 65 (.pack [4]) (.split 75 (.pack [8]) (.split 76 (.pack [9]) (.split 77 (.pack [10]) (.split 88 (.pack [9]) (.split 103 (.pack [0]) (.split 130 (.pack [3]) (.zero 1)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 509. -/
theorem checked509 : checkParitySearch 8 (fun q => (rows509 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed509.contains) tree509 0xffe5fe7ffdffffffff4bf7bff3fffffefffaffefffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 510. -/
noncomputable def rows510 : Nat := (Nat.lor 0x8000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000044008000c018000098008013010602e03a80120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000002000001800080000000000000000010010000000000000000000000000000000100000018024000000000000000000800000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000000000008000000c0120000000000000000004 (Nat.shiftLeft 0xa000000000000000800000100120000000000000000000000000000000000000018000000000000004000000800900000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 510. -/
noncomputable def allowed510 : List Nat := [0x8000000000000,0x20000000000000,0x800000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 510. -/
noncomputable def tree510 : ParitySearchTree := (.split 21 (.pack [5]) (.split 24 (.pack [7]) (.split 35 (.pack [8]) (.split 37 (.pack [11]) (.split 39 (.pack [10]) (.split 40 (.pack [12]) (.split 41 (.pack [13]) (.split 49 (.pack [11]) (.split 50 (.pack [15]) (.split 51 .done (.split 53 .done (.split 61 (.pack [14]) (.split 62 (.pack [15]) (.split 68 (.pack [16]) (.split 76 (.pack [17]) (.split 77 (.pack [0]) (.split 80 (.pack [0]) (.split 91 (.pack [0]) (.split 103 (.pack [3]) (.split 104 (.pack [3]) (.split 107 (.pack [4]) (.split 127 (.pack [1]) (.split 128 (.pack [2]) (.split 138 (.pack [11]) (.split 139 (.pack [6]) (.split 155 .done (.split 166 (.pack [11]) (.split 170 .done (.zero 9)))))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 510. -/
theorem checked510 : checkParitySearch 8 (fun q => (rows510 >>> (256*q)) &&& (2^256-1)) 0x200 (allowed510.contains) tree510 0xffe5f99ff3fffffffffff6fff3ffd7fefffaff9ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 511. -/
noncomputable def rows511 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 511. -/
noncomputable def allowed511 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 511. -/
noncomputable def tree511 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 133 (.pack [7]) (.split 134 (.pack [7]) (.split 169 (.pack [8]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 511. -/
theorem checked511 : checkParitySearch 8 (fun q => (rows511 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed511.contains) tree511 0xffe4ffcfffffffffff03fe3ffffff4fffffe7ffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 512. -/
noncomputable def rows512 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000040000014001000000000000000000200200000000000000000000060000000012000000400081b818f000000000009008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 512. -/
noncomputable def allowed512 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 512. -/
noncomputable def tree512 : ParitySearchTree := (.split 3 (.pack [2]) (.split 12 (.pack [3]) (.split 15 (.pack [4]) (.split 60 (.pack [7]) (.split 61 (.pack [8]) (.split 62 (.pack [9]) (.split 63 (.pack [10]) (.split 67 (.pack [11]) (.split 68 (.pack [12]) (.split 75 (.pack [13]) (.split 76 (.pack [14]) (.split 77 (.pack [15]) (.split 79 .done (.split 80 .done (.split 87 (.pack [13]) (.split 102 (.pack [1]) (.split 129 (.pack [5]) (.split 132 (.pack [6]) (.split 169 (.pack [10]) (.split 170 (.pack [10]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 512. -/
theorem checked512 : checkParitySearch 8 (fun q => (rows512 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed512.contains) tree512 0xffe3ff3fffffffffffb7f0bfffffdffc7ff9ffffffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 513. -/
noncomputable def rows513 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000006000000000000000dc00001b818f00000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 513. -/
noncomputable def allowed513 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 513. -/
noncomputable def tree513 : ParitySearchTree := (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 63 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 75 (.pack [11]) (.split 76 (.pack [12]) (.split 77 (.pack [13]) (.split 79 .done (.split 80 .done (.split 102 (.pack [1]) (.split 103 (.pack [2]) (.split 104 (.pack [0]) (.split 106 (.pack [3]) (.split 107 (.pack [3]) (.split 169 (.pack [8]) (.split 170 (.pack [8]) (.zero 7)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 513. -/
theorem checked513 : checkParitySearch 8 (fun q => (rows513 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed513.contains) tree513 0xffe3fe1ffdfffffffffff03fffffcfff7ff9ffeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 514. -/
noncomputable def rows514 : Nat := (Nat.lor 0x300000000000000010000002002400000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000000030000000040000000009000c00d800000000002000000000000000000000040018006006c2000000000480140148000020800010 (Nat.shiftLeft 0x1800000000000000400000080090000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000018000000000000004000000800900000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 514. -/
noncomputable def allowed514 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 514. -/
noncomputable def tree514 : ParitySearchTree := (.split 4 (.pack [6]) (.split 23 (.pack [7]) (.split 29 (.pack [10]) (.split 51 (.pack [1]) (.split 54 (.pack [15]) (.split 56 (.pack [16]) (.split 66 (.pack [17]) (.split 68 (.pack [18]) (.split 79 .done (.split 82 (.pack [2]) (.split 121 (.pack [11]) (.split 126 (.pack [3]) (.split 127 (.pack [4]) (.split 129 (.pack [13]) (.split 130 (.pack [5]) (.split 141 (.pack [8]) (.split 142 (.pack [9]) (.split 155 (.pack [14]) (.split 156 (.pack [12]) (.split 170 (.pack [17]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 514. -/
theorem checked514 : checkParitySearch 8 (fun q => (rows514 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed514.contains) tree514 0xffe3fbbff7ffffffffb7f0bfffffdffdfff9ffbfffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 515. -/
noncomputable def rows515 : Nat := 0x3000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000060000000060000000000001801b000000000003003600000000000000000000060000000010000000000001801b000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 515. -/
noncomputable def allowed515 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 515. -/
noncomputable def tree515 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [0]) (.split 5 (.pack [1]) (.split 16 (.pack [4]) (.split 17 (.pack [5]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 79 (.pack [0]) (.split 80 (.pack [1]) (.split 133 (.pack [6]) (.split 134 (.pack [6]) (.split 169 (.pack [7]) (.split 170 (.pack [2]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 515. -/
theorem checked515 : checkParitySearch 8 (fun q => (rows515 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed515.contains) tree515 0xffe3bfffffbfffffff18ff8ffcfff7fffffedffdfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 516. -/
noncomputable def rows516 : Nat := 0x20000018000000000000000000000100120000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000180038030000000000000000000000c00c401f800000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000010000005002400000000000000000080000000000000000000001d0060100120010010004000408280480000800000a2

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 516. -/
noncomputable def allowed516 : List Nat := [0x8,0x10]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 516. -/
noncomputable def tree516 : ParitySearchTree := (.split 3 .done (.split 4 .done (.split 5 (.pack [0]) (.split 6 (.pack [4]) (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 18 (.pack [7]) (.split 22 (.pack [5]) (.split 23 (.pack [6]) (.split 34 (.pack [9]) (.split 35 (.pack [10]) (.split 124 (.pack [1]) (.split 125 (.pack [8]) (.split 135 (.pack [9]) (.split 136 (.pack [10]) (.split 137 (.pack [9]) (.split 151 (.pack [11]) (.split 152 (.pack [11]) (.zero 3)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 516. -/
theorem checked516 : checkParitySearch 8 (fun q => (rows516 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed516.contains) tree516 0xffdfffffffffff7df93ff57fcffe3ffefffffffe4ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 517. -/
noncomputable def rows517 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000002000001800080000000000000000010010000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 517. -/
noncomputable def allowed517 : List Nat := [0x8,0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 517. -/
noncomputable def tree517 : ParitySearchTree := (.split 0 (.pack [1]) (.split 1 (.pack [0]) (.split 2 (.pack [2]) (.split 3 .done (.split 4 .done (.split 5 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 132 (.pack [8]) (.split 133 (.pack [9]) (.split 134 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 517. -/
theorem checked517 : checkParitySearch 8 (fun q => (rows517 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed517.contains) tree517 0xffdfffffffffff6ff91ff57fcbfe3ffefffffffe7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 518. -/
noncomputable def rows518 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000200000030000000000000000000001001200000000000000000000000100180008030005000000000000000800500d00090000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000800100080010030006001200000004004000b002000000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 518. -/
noncomputable def allowed518 : List Nat := [0x400000000,0x800000000000,0x8000000000000000000000000000000000,0x80000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 518. -/
noncomputable def tree518 : ParitySearchTree := (.split 4 (.pack [0]) (.split 7 (.pack [2]) (.split 20 (.pack [5]) (.split 22 (.pack [6]) (.split 23 (.pack [7]) (.split 32 (.pack [8]) (.split 34 .done (.split 47 .done (.split 108 (.pack [5]) (.split 110 (.pack [10]) (.split 124 (.pack [2]) (.split 125 (.pack [3]) (.split 135 .done (.split 151 .done (.split 152 (.pack [1]) (.split 164 (.pack [9]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 518. -/
theorem checked518 : checkParitySearch 8 (fun q => (rows518 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed518.contains) tree518 0xffdf7fba7fafff7fffffffffffffd2fff9fd7fff3ffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 519. -/
noncomputable def rows519 : Nat := 0x50000000000000004000000800900000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000005000000000000000a001c014015003f0000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000006004000401400280000000000000030016020004800000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 519. -/
noncomputable def allowed519 : List Nat := [0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 519. -/
noncomputable def tree519 : ParitySearchTree := (.split 48 (.pack [3]) (.split 49 (.pack [3]) (.split 50 .done (.split 51 (.pack [6]) (.split 52 (.pack [7]) (.split 53 (.pack [8]) (.split 64 (.pack [9]) (.split 66 (.pack [6]) (.split 68 (.pack [8]) (.split 78 (.pack [0]) (.split 80 (.pack [1]) (.split 90 (.pack [1]) (.split 91 (.pack [1]) (.split 92 (.pack [0]) (.split 105 (.pack [2]) (.split 107 (.pack [2]) (.split 168 (.pack [4]) (.split 170 (.pack [10]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 519. -/
theorem checked519 : checkParitySearch 8 (fun q => (rows519 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed519.contains) tree519 0xffdf7f4bfe77ff7fffffffffffffd2fffffd7ff1fffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 520. -/
noncomputable def rows520 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000080000060000000000000000000000400480000000000000000000005000000002000000000000140168000000000010012000000000000000000000500000000500000000000014016800000000002802d00000000000000000000000000000000040000006009000000000000000000200000000000000000000000000a0000000040000000009002802d000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 520. -/
noncomputable def allowed520 : List Nat := [0x1,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 520. -/
noncomputable def tree520 : ParitySearchTree := (.split 0 .done (.split 2 .done (.split 3 (.pack [4]) (.split 5 (.pack [1]) (.split 15 (.pack [5]) (.split 17 (.pack [6]) (.split 63 (.pack [0]) (.split 65 (.pack [0]) (.split 66 (.pack [9]) (.split 68 (.pack [10]) (.split 78 (.pack [3]) (.split 80 (.pack [1]) (.split 132 (.pack [7]) (.split 134 (.pack [7]) (.split 168 (.pack [8]) (.split 170 (.pack [3]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 520. -/
theorem checked520 : checkParitySearch 8 (fun q => (rows520 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed520.contains) tree520 0xffdbffbfffffff6ffe03fe3fdfffeffffffdfffe7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 521. -/
noncomputable def rows521 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000001c0000000000000000000000000000e00fc000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001c0000000000000000000000000000e00fc00000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000180000000000006000000000000000c00d801801b0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 521. -/
noncomputable def allowed521 : List Nat := [0x400000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 521. -/
noncomputable def tree521 : ParitySearchTree := (.split 30 (.pack [1]) (.split 31 (.pack [2]) (.split 32 (.pack [3]) (.split 33 (.pack [5]) (.split 34 (.pack [7]) (.split 35 (.pack [6]) (.split 45 (.pack [0]) (.split 46 .done (.split 47 .done (.split 162 (.pack [9]) (.split 163 (.pack [9]) (.split 164 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 521. -/
theorem checked521 : checkParitySearch 8 (fun q => (rows521 >>> (256*q)) &&& (2^256-1)) 0x91 (allowed521.contains) tree521 0xffdbffa07fc7ff6ffeffffffdfffd7fffffdffffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 522. -/
noncomputable def rows522 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000000040000030000000000000000000000200240000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 522. -/
noncomputable def allowed522 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 522. -/
noncomputable def tree522 : ParitySearchTree := (.split 45 (.pack [0]) (.split 46 (.pack [1]) (.split 47 (.pack [2]) (.split 48 .done (.split 49 .done (.split 50 .done (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 177 (.pack [8]) (.split 178 (.pack [8]) (.split 179 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 522. -/
theorem checked522 : checkParitySearch 8 (fun q => (rows522 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed522.contains) tree522 0xffdbff43fe77ff7fffffffffffffd7fffffd3ff1fffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 523. -/
noncomputable def rows523 : Nat := 0x400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000003000700600000000000000000000018018803f00000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 523. -/
noncomputable def allowed523 : List Nat := [0x1,0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 523. -/
noncomputable def tree523 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 (.pack [0]) (.split 3 (.pack [2]) (.split 4 (.pack [3]) (.split 5 (.pack [4]) (.split 15 (.pack [5]) (.split 19 (.pack [3]) (.split 20 (.pack [4]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 121 (.pack [6]) (.split 122 (.pack [6]) (.split 132 (.pack [7]) (.split 133 (.pack [8]) (.split 134 (.pack [7]) (.split 148 (.pack [9]) (.split 149 (.pack [9]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 523. -/
theorem checked523 : checkParitySearch 8 (fun q => (rows523 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed523.contains) tree523 0xffcfffffffffffedff23f8fff7ffc7fe7fffffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 524. -/
noncomputable def rows524 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000004005000a00000000c0040018013008001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000a00a000008008000400400300020120000000040008040000000000000000000000005a00000000200e00500188168082000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 524. -/
noncomputable def allowed524 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x400000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 524. -/
noncomputable def tree524 : ParitySearchTree := (.split 37 (.pack [3]) (.split 40 (.pack [4]) (.split 55 (.pack [8]) (.split 64 (.pack [1]) (.split 65 (.pack [9]) (.split 68 (.pack [10]) (.split 79 .done (.split 80 .done (.split 94 .done (.split 106 .done (.split 107 (.pack [2]) (.split 141 (.pack [7]) (.split 143 (.pack [0]) (.split 156 (.pack [10]) (.split 158 (.pack [5]) (.split 170 (.pack [7]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 524. -/
theorem checked524 : checkParitySearch 8 (fun q => (rows524 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed524.contains) tree524 0xffcfffffffffffdf7df7fd3ffaff7ffe7fffffffd2fd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 525. -/
noncomputable def rows525 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000004000a00a00000000c000801801a000201200000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000004a00c00c008008004400a01b008a001009000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 525. -/
noncomputable def allowed525 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x80000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 525. -/
noncomputable def tree525 : ParitySearchTree := (.split 37 (.pack [3]) (.split 40 (.pack [5]) (.split 49 (.pack [6]) (.split 65 (.pack [9]) (.split 67 (.pack [11]) (.split 68 (.pack [10]) (.split 79 .done (.split 80 .done (.split 91 .done (.split 106 .done (.split 107 (.pack [0]) (.split 141 (.pack [1]) (.split 143 (.pack [2]) (.split 153 (.pack [9]) (.split 155 (.pack [4]) (.split 170 (.pack [8]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 525. -/
theorem checked525 : checkParitySearch 8 (fun q => (rows525 >>> (256*q)) &&& (2^256-1)) 0x81 (allowed525.contains) tree525 0xffcfffffffffffdbfed7fbbffbffaffe7fffffffd7fca 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 526. -/
noncomputable def rows526 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000004005000a00000000c0040018013008001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000002c006000c20004001400400d80450040009000100100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 526. -/
noncomputable def allowed526 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x400000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 526. -/
noncomputable def tree526 : ParitySearchTree := (.split 37 (.pack [3]) (.split 40 (.pack [4]) (.split 55 (.pack [8]) (.split 64 (.pack [11]) (.split 65 (.pack [9]) (.split 68 (.pack [10]) (.split 79 .done (.split 80 .done (.split 94 .done (.split 106 .done (.split 107 (.pack [0]) (.split 141 (.pack [1]) (.split 143 (.pack [2]) (.split 156 (.pack [10]) (.split 158 (.pack [5]) (.split 170 (.pack [7]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 526. -/
theorem checked526 : checkParitySearch 8 (fun q => (rows526 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed526.contains) tree526 0xffcfffffffffffdbfddbfd7ffbff77fe7fffffffd7fd1 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 527. -/
noncomputable def rows527 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c00200000000000000000040040000000000000000000004005600c000008004004001a0008083009000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 527. -/
noncomputable def allowed527 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x400000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 527. -/
noncomputable def tree527 : ParitySearchTree := (.split 2 (.pack [1]) (.split 36 (.pack [5]) (.split 39 (.pack [6]) (.split 48 (.pack [8]) (.split 49 (.pack [9]) (.split 55 (.pack [12]) (.split 63 (.pack [13]) (.split 77 (.pack [14]) (.split 79 .done (.split 80 .done (.split 94 .done (.split 106 .done (.split 119 (.pack [4]) (.split 142 (.pack [2]) (.split 143 (.pack [3]) (.split 153 (.pack [5]) (.split 154 (.pack [11]) (.split 156 (.pack [6]) (.split 158 (.pack [7]) (.split 170 (.pack [10]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 527. -/
theorem checked527 : checkParitySearch 8 (fun q => (rows527 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed527.contains) tree527 0xffcfffffffffffdbf97ff53ffbfe7ffe7fffffffd7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 528. -/
noncomputable def rows528 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000008000001c01f80000000000200240000000000000000000a00a00000800800040040030002012000000004000804000000000000000000000000060060000080080000002013800301b000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 528. -/
noncomputable def allowed528 : List Nat := [0x20000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 528. -/
noncomputable def tree528 : ParitySearchTree := (.split 2 (.pack [1]) (.split 5 (.pack [3]) (.split 17 .done (.split 63 (.pack [7]) (.split 64 (.pack [1]) (.split 65 (.pack [5]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [6]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 107 (.pack [0]) (.split 134 (.pack [4]) (.zero 2)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 528. -/
theorem checked528 : checkParitySearch 8 (fun q => (rows528 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed528.contains) tree528 0xffcfffffffffffcd7f97f93ffefffffe7fffffffe2fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 529. -/
noncomputable def rows529 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000008000001c01f80000000000200240000000000000000000c00c00000800800080080028001009000000004000804000000000000000000000000060060000080080000002013800301b000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 529. -/
noncomputable def allowed529 : List Nat := [0x20000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 529. -/
noncomputable def tree529 : ParitySearchTree := (.split 2 (.pack [1]) (.split 5 (.pack [3]) (.split 17 .done (.split 63 (.pack [1]) (.split 64 (.pack [7]) (.split 65 (.pack [5]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [6]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 107 (.pack [0]) (.split 134 (.pack [4]) (.zero 2)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 529. -/
theorem checked529 : checkParitySearch 8 (fun q => (rows529 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed529.contains) tree529 0xffcfffffffffffcbbf9bf93fff7ffffe7fffffffe1fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 530. -/
noncomputable def rows530 : Nat := 0x300000000000000080000010012000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000004000a00a00000000c000801801a00020120000000000000000000000000000004006000c00000000a002001401280400090000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000100000050024000000000000000000800000000000000000000000000030002004000a00a004800000000001801a0002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 530. -/
noncomputable def allowed530 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 530. -/
noncomputable def tree530 : ParitySearchTree := (.split 1 (.pack [2]) (.split 17 (.pack [8]) (.split 19 (.pack [3]) (.split 20 (.pack [4]) (.split 31 (.pack [5]) (.split 32 (.pack [6]) (.split 79 .done (.split 82 (.pack [1]) (.split 93 (.pack [8]) (.split 95 (.pack [10]) (.split 105 (.pack [7]) (.split 107 (.pack [7]) (.split 122 (.pack [8]) (.split 133 (.pack [6]) (.split 148 (.pack [9]) (.split 149 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 530. -/
theorem checked530 : checkParitySearch 8 (fun q => (rows530 >>> (256*q)) &&& (2^256-1)) 0x101 (allowed530.contains) tree530 0xffcfffffffffffc9fef7fbbfffffaffe7fffffffe7fca 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 531. -/
noncomputable def rows531 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000004005000a00000000c004001801300800120000000000000000000000000000004000c00c00000000a00040140160001009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000028001004000c00c002400000000001401600010000000000000000000000000006002000800a00140090000000000030026010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 531. -/
noncomputable def allowed531 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 531. -/
noncomputable def tree531 : ParitySearchTree := (.split 4 (.pack [2]) (.split 13 (.pack [3]) (.split 14 (.pack [4]) (.split 17 (.pack [1]) (.split 28 (.pack [5]) (.split 29 (.pack [6]) (.split 76 (.pack [12]) (.split 79 .done (.split 90 (.pack [8]) (.split 92 (.pack [11]) (.split 105 (.pack [8]) (.split 107 (.pack [8]) (.split 119 (.pack [9]) (.split 133 (.pack [7]) (.split 145 (.pack [10]) (.split 146 (.pack [10]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 531. -/
theorem checked531 : checkParitySearch 8 (fun q => (rows531 >>> (256*q)) &&& (2^256-1)) 0x201 (allowed531.contains) tree531 0xffcfffffffffffc9fdfbfd7fffff77fe7fffffffe7fd1 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 532. -/
noncomputable def rows532 : Nat := 0x3000000000000000800000100120000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000004000a00a00000000c000801801a000201200000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000280001000200080010050020004800000008008001a0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 532. -/
noncomputable def allowed532 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x80000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 532. -/
noncomputable def tree532 : ParitySearchTree := (.split 37 (.pack [4]) (.split 40 (.pack [6]) (.split 49 (.pack [7]) (.split 65 (.pack [10]) (.split 67 (.pack [0]) (.split 68 (.pack [11]) (.split 79 .done (.split 80 .done (.split 91 .done (.split 106 .done (.split 107 (.pack [1]) (.split 141 (.pack [2]) (.split 143 (.pack [3]) (.split 153 (.pack [10]) (.split 155 (.pack [5]) (.split 170 (.pack [9]) (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 532. -/
theorem checked532 : checkParitySearch 8 (fun q => (rows532 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed532.contains) tree532 0xffcffffffffffefbfdf7f9bfbbffeffe7ffffffe97ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 533. -/
noncomputable def rows533 : Nat := 0x300000000000000010000002002400000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000140028028005000000000000000000a00a0016800000000000000000000000000000040000008000001c01f800000000002002400000000000000000000000000000008000000c002000000000000000000400400000000000000000000000030006000040008000008001e00c001b000000020000000000000000000000000060060000080080000002013800301b000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 533. -/
noncomputable def allowed533 : List Nat := [0x20000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 533. -/
noncomputable def tree533 : ParitySearchTree := (.split 2 (.pack [2]) (.split 5 (.pack [4]) (.split 17 .done (.split 63 (.pack [8]) (.split 64 (.pack [9]) (.split 65 (.pack [6]) (.split 66 (.pack [10]) (.split 67 (.pack [1]) (.split 68 (.pack [7]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 107 (.pack [0]) (.split 134 (.pack [5]) (.zero 3)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 533. -/
theorem checked533 : checkParitySearch 8 (fun q => (rows533 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed533.contains) tree533 0xffcffffffffffee9fd9ff93fbffffffe7ffffffea7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 534. -/
noncomputable def rows534 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000000000c00c00000000c0018018018000603600000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000002400000d8000000090000012010400900820000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a00000000000000000000010012

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 534. -/
noncomputable def allowed534 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x80000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 534. -/
noncomputable def tree534 : ParitySearchTree := (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 40 (.pack [6]) (.split 41 (.pack [7]) (.split 49 (.pack [8]) (.split 50 (.pack [9]) (.split 67 (.pack [11]) (.split 68 (.pack [12]) (.split 79 .done (.split 80 .done (.split 91 .done (.split 92 (.pack [3]) (.split 106 .done (.split 107 (.pack [0]) (.split 142 (.pack [1]) (.split 143 (.pack [2]) (.split 154 (.pack [4]) (.split 155 (.pack [5]) (.zero 10)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 534. -/
theorem checked534 : checkParitySearch 8 (fun q => (rows534 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed534.contains) tree534 0xffcffedffdffffdbfff7f9bffbffeffd7fffffefd7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 535. -/
noncomputable def rows535 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000008000001c01f800000000002002400000000000000000000000000000008000000c0020000000000000000004004000000000000000000000400000000000080080010002011800703f000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 535. -/
noncomputable def allowed535 : List Nat := [0x20000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 535. -/
noncomputable def tree535 : ParitySearchTree := (.split 2 (.pack [1]) (.split 5 (.pack [3]) (.split 17 .done (.split 63 (.pack [5]) (.split 64 (.pack [6]) (.split 65 (.pack [7]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 107 (.pack [0]) (.split 134 (.pack [4]) (.zero 2)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 535. -/
theorem checked535 : checkParitySearch 8 (fun q => (rows535 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed535.contains) tree535 0xffcffedffdffffc9ff9ff93ffffffffd7fffffefe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 536. -/
noncomputable def rows536 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000004000a00a00000000c000801801a0002012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000005a00000001000e00880380168082000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 536. -/
noncomputable def allowed536 : List Nat := [0x80000000000000000000,0x100000000000000000000,0x80000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 536. -/
noncomputable def tree536 : ParitySearchTree := (.split 37 (.pack [6]) (.split 40 (.pack [8]) (.split 49 (.pack [6]) (.split 65 (.pack [9]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 79 .done (.split 80 .done (.split 91 .done (.split 106 .done (.split 107 (.pack [1]) (.split 141 (.pack [2]) (.split 143 (.pack [3]) (.split 153 (.pack [4]) (.split 155 (.pack [5]) (.split 170 (.pack [0]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 536. -/
theorem checked536 : checkParitySearch 8 (fun q => (rows536 >>> (256*q)) &&& (2^256-1)) 0x81 (allowed536.contains) tree536 0xffcffdbffbffffdbfff7f9bffbffeffcffffffdfd7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 537. -/
noncomputable def rows537 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000008000001c01f800000000002002400000000000000000000000000000008000000c0020000000000000000004004000000000000000000000400000000000080080010002011800703f000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 537. -/
noncomputable def allowed537 : List Nat := [0x20000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 537. -/
noncomputable def tree537 : ParitySearchTree := (.split 2 (.pack [1]) (.split 5 (.pack [3]) (.split 17 .done (.split 63 (.pack [5]) (.split 64 (.pack [6]) (.split 65 (.pack [7]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 107 (.pack [0]) (.split 134 (.pack [4]) (.zero 2)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 537. -/
theorem checked537 : checkParitySearch 8 (fun q => (rows537 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed537.contains) tree537 0xffcffdbffbffffc9ff9ff93ffffffffcffffffdfe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 538. -/
noncomputable def rows538 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000400000000000000080000010012003803f0000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000040000008009001c01f8000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 538. -/
noncomputable def allowed538 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 538. -/
noncomputable def tree538 : ParitySearchTree := (.split 5 (.pack [1]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 80 .done (.split 83 (.pack [9]) (.split 95 (.pack [3]) (.split 122 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 538. -/
theorem checked538 : checkParitySearch 8 (fun q => (rows538 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed538.contains) tree538 0xffcffcd7f97ffffffffff93ff3ffffffafffffcbfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 539. -/
noncomputable def rows539 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000400000000000000080000010012003803f0000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000040000008009001c01f8000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 539. -/
noncomputable def allowed539 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 539. -/
noncomputable def tree539 : ParitySearchTree := (.split 5 (.pack [1]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 80 .done (.split 83 (.pack [9]) (.split 95 (.pack [3]) (.split 122 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 539. -/
theorem checked539 : checkParitySearch 8 (fun q => (rows539 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed539.contains) tree539 0xffcffcbbf9bffffffffff93ff3ffffff9fffffcdfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 540. -/
noncomputable def rows540 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000400000000000000080000010012003803f0000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000000040000008009001c01f8000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 540. -/
noncomputable def allowed540 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 540. -/
noncomputable def tree540 : ParitySearchTree := (.split 5 (.pack [1]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 80 .done (.split 83 (.pack [9]) (.split 95 (.pack [3]) (.split 122 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 540. -/
theorem checked540 : checkParitySearch 8 (fun q => (rows540 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed540.contains) tree540 0xffcffc9ff9ffffffffdbf97ff3fff7ffffffffcfffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 541. -/
noncomputable def rows541 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000400000000000000080000010012003803f0000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000000040000008009001c01f8000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 541. -/
noncomputable def allowed541 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 541. -/
noncomputable def tree541 : ParitySearchTree := (.split 5 (.pack [1]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 80 .done (.split 83 (.pack [9]) (.split 95 (.pack [3]) (.split 122 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 541. -/
theorem checked541 : checkParitySearch 8 (fun q => (rows541 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed541.contains) tree541 0xffcffc9ff9ffffffffb7f9bff3ffefffffffffcfffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 542. -/
noncomputable def rows542 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000400000000000000080000010012003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 542. -/
noncomputable def allowed542 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 542. -/
noncomputable def tree542 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [3]) (.split 49 (.pack [4]) (.split 50 (.pack [5]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 .done (.split 92 (.pack [6]) (.split 119 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 542. -/
theorem checked542 : checkParitySearch 8 (fun q => (rows542 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed542.contains) tree542 0xffcffc9ff9fffffffedffb3ff3ffbfffffffffcffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 543. -/
noncomputable def rows543 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000400000000000000080000010012003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 543. -/
noncomputable def allowed543 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 543. -/
noncomputable def tree543 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [3]) (.split 49 (.pack [4]) (.split 50 (.pack [5]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 .done (.split 92 (.pack [6]) (.split 119 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 543. -/
theorem checked543 : checkParitySearch 8 (fun q => (rows543 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed543.contains) tree543 0xffcffc9ff9fffffffdbffd3ff3ff7fffffffffcffffd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 544. -/
noncomputable def rows544 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000400000000000000080000010012003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 544. -/
noncomputable def allowed544 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 544. -/
noncomputable def tree544 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [3]) (.split 49 (.pack [4]) (.split 50 (.pack [5]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 .done (.split 92 (.pack [6]) (.split 119 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 544. -/
theorem checked544 : checkParitySearch 8 (fun q => (rows544 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed544.contains) tree544 0xffcffc9ff9ffffedffdff93ff7ffffffffffffcfcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 545. -/
noncomputable def rows545 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000400000000000000080000010012003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 545. -/
noncomputable def allowed545 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 545. -/
noncomputable def tree545 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [3]) (.split 49 (.pack [4]) (.split 50 (.pack [5]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 .done (.split 92 (.pack [6]) (.split 119 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 545. -/
theorem checked545 : checkParitySearch 8 (fun q => (rows545 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed545.contains) tree545 0xffcffc9ff9ffffdbffbff93ffbffffffffffffcfd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 546. -/
noncomputable def rows546 : Nat := 0x30000000000000008000001001200000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000001000000500240000000000000000008000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000020006001000c00a00480000000000100110026

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 546. -/
noncomputable def allowed546 : List Nat := [0x80000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 546. -/
noncomputable def tree546 : ParitySearchTree := (.split 1 (.pack [3]) (.split 2 (.pack [4]) (.split 5 (.pack [1]) (.split 16 (.pack [5]) (.split 20 (.pack [7]) (.split 32 (.pack [9]) (.split 79 .done (.split 82 (.pack [2]) (.split 93 (.pack [1]) (.split 95 (.pack [12]) (.split 106 .done (.split 107 (.pack [10]) (.split 120 (.pack [6]) (.split 133 (.pack [9]) (.split 134 (.pack [8]) (.split 149 (.pack [11]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 546. -/
theorem checked546 : checkParitySearch 8 (fun q => (rows546 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed546.contains) tree546 0xffcffb7ff7ffffdbfcdfff3ffbff3fffffffffbfd7fe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 547. -/
noncomputable def rows547 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000a000000048000008400201d01ea00000000002402000000000000000000000000030000000040000000009000c00d800000000002000000000000000000000000006000040008008000000e01e001b00000002002000000000000000000000000006060020008004001801501e001b000030026010000000000000000000000000003a001000800c001800480000000001d01e2008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 547. -/
noncomputable def allowed547 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 547. -/
noncomputable def tree547 : ParitySearchTree := (.split 5 (.pack [5]) (.split 17 (.pack [0]) (.split 48 (.pack [7]) (.split 49 (.pack [8]) (.split 51 (.pack [3]) (.split 52 (.pack [3]) (.split 65 (.pack [10]) (.split 66 (.pack [13]) (.split 67 (.pack [14]) (.split 68 (.pack [11]) (.split 77 (.pack [12]) (.split 78 (.pack [1]) (.split 79 .done (.split 107 (.pack [9]) (.split 119 (.pack [4]) (.split 134 (.pack [6]) (.split 153 (.pack [10]) (.split 154 (.pack [10]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 547. -/
theorem checked547 : checkParitySearch 8 (fun q => (rows547 >>> (256*q)) &&& (2^256-1)) 0x14 (allowed547.contains) tree547 0xffcffb7ff7ffffc9ffd7f9bfffffefffffffffbfe7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 548. -/
noncomputable def rows548 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000003f0000000000000000000000000001f81c7000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000100000050000000000000000000000800900000000000000000000000c000000048000008800201c81f100000000002402000000000000000000000000006000040008008000000e01e001b0000000200200000000000000000000000000006002000800a00140090000000000030026010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 548. -/
noncomputable def allowed548 : List Nat := [0x20000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 548. -/
noncomputable def tree548 : ParitySearchTree := (.split 4 (.pack [3]) (.split 13 (.pack [4]) (.split 14 (.pack [5]) (.split 17 .done (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 76 (.pack [11]) (.split 79 .done (.split 90 (.pack [1]) (.split 92 (.pack [10]) (.split 105 (.pack [1]) (.split 107 (.pack [8]) (.split 119 (.pack [2]) (.split 133 (.pack [7]) (.split 145 (.pack [9]) (.split 146 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 548. -/
theorem checked548 : checkParitySearch 8 (fun q => (rows548 >>> (256*q)) &&& (2^256-1)) 0x7 (allowed548.contains) tree548 0xffcffb7ff7ffffc9ffbbf97ffffff7ffffffffbfe7ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 549. -/
noncomputable def rows549 : Nat := 0x30000000000000008000001001200000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000000000060000000080000010012001801b000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000300000000240000028000003c03b8000000000120104000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000100000050024000000000000000000800000000000000000000000000030002004000a00a004800000000001801a0002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 549. -/
noncomputable def allowed549 : List Nat := [0x20000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 549. -/
noncomputable def tree549 : ParitySearchTree := (.split 1 (.pack [2]) (.split 17 .done (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 31 (.pack [6]) (.split 32 (.pack [7]) (.split 79 .done (.split 82 (.pack [1]) (.split 93 (.pack [3]) (.split 95 (.pack [10]) (.split 105 (.pack [3]) (.split 107 (.pack [8]) (.split 122 (.pack [3]) (.split 133 (.pack [7]) (.split 148 (.pack [9]) (.split 149 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 549. -/
theorem checked549 : checkParitySearch 8 (fun q => (rows549 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed549.contains) tree549 0xffcffb7ff7ffffc9febffb3fffffbfffffffffbfe7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 550. -/
noncomputable def rows550 : Nat := (Nat.lor 0xa000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000040010002006000c0c0040018013008003202000480000000000000000000000280000000240000018000005c057800000000012010400000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000003030002004000400c005401380d80001801a0002000000000000000000000000060000000080000000012001801b000000000004 (Nat.shiftLeft 0x180000000000000040000008009000000000000000000000000000000000000030000000000000001000000200240000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 550. -/
noncomputable def allowed550 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 550. -/
noncomputable def tree550 : ParitySearchTree := (.split 2 (.pack [4]) (.split 8 (.pack [3]) (.split 17 (.pack [6]) (.split 20 (.pack [7]) (.split 63 (.pack [14]) (.split 64 (.pack [15]) (.split 65 (.pack [11]) (.split 66 (.pack [16]) (.split 68 (.pack [12]) (.split 70 (.pack [13]) (.split 78 (.pack [1]) (.split 79 .done (.split 80 (.pack [0]) (.split 82 (.pack [2]) (.split 107 (.pack [10]) (.split 108 (.pack [16]) (.split 134 (.pack [8]) (.split 137 (.pack [9]) (.split 171 (.pack [17]) (.split 173 (.pack [16]) (.zero 5)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 550. -/
theorem checked550 : checkParitySearch 8 (fun q => (rows550 >>> (256*q)) &&& (2^256-1)) 0x60 (allowed550.contains) tree550 0xffcffb7ff7ffffc9fddffd3fffff7fffffffffbfe7fd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 551. -/
noncomputable def rows551 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000006040000000000000c00d801801b00002002400000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 551. -/
noncomputable def allowed551 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 551. -/
noncomputable def tree551 : ParitySearchTree := (.split 12 (.pack [0]) (.split 13 (.pack [1]) (.split 14 (.pack [2]) (.split 15 (.pack [3]) (.split 16 (.pack [3]) (.split 17 .done (.split 27 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 144 (.pack [9]) (.split 145 (.pack [10]) (.split 146 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 551. -/
theorem checked551 : checkParitySearch 8 (fun q => (rows551 >>> (256*q)) &&& (2^256-1)) 0x18 (allowed551.contains) tree551 0xffcffb7ff7ffff81ff1ff93fefffffffffffffbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 552. -/
noncomputable def rows552 : Nat := 0x300000000000000010000002002400000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000000060000000080000010012001801b0000000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000008009006006c000000000000000000400000410000000000000000000028003000000002002000c000804400d8000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 552. -/
noncomputable def allowed552 : List Nat := [0x80000000000000000000,0x400000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 552. -/
noncomputable def tree552 : ParitySearchTree := (.split 4 (.pack [2]) (.split 51 (.pack [3]) (.split 52 (.pack [3]) (.split 54 (.pack [6]) (.split 55 (.pack [7]) (.split 66 (.pack [8]) (.split 70 (.pack [7]) (.split 79 .done (.split 94 .done (.split 95 (.pack [5]) (.split 109 (.pack [1]) (.split 121 (.pack [1]) (.split 156 (.pack [5]) (.split 157 (.pack [5]) (.split 171 (.pack [4]) (.split 173 (.pack [8]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 552. -/
theorem checked552 : checkParitySearch 8 (fun q => (rows552 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed552.contains) tree552 0xffcffb7ff7fffefbfffffd3fbbff7fffffffffbe97fd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 553. -/
noncomputable def rows553 : Nat := (Nat.lor 0x280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000010002003000601001e000001802380b01000240000080000000000000000000000000c00000000200000000048030036000000000001 (Nat.shiftLeft 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 553. -/
noncomputable def allowed553 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 553. -/
noncomputable def tree553 : ParitySearchTree := (.split 3 (.pack [4]) (.split 26 (.pack [7]) (.split 29 (.pack [9]) (.split 44 (.pack [12]) (.split 52 (.pack [0]) (.split 53 (.pack [0]) (.split 55 (.pack [15]) (.split 63 (.pack [16]) (.split 64 (.pack [17]) (.split 65 (.pack [18]) (.split 69 (.pack [14]) (.split 79 .done (.split 80 .done (.split 105 (.pack [5]) (.split 106 (.pack [4]) (.split 107 (.pack [4]) (.split 108 (.pack [6]) (.split 120 (.pack [10]) (.split 129 (.pack [2]) (.split 130 (.pack [3]) (.split 144 (.pack [13]) (.split 145 (.pack [8]) (.split 157 (.pack [11]) (.split 172 (.pack [13]) (.zero 1)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 553. -/
theorem checked553 : checkParitySearch 8 (fun q => (rows553 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed553.contains) tree553 0xffcffadffdffffffffffb83f9fff3fef7fdfffeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 554. -/
noncomputable def rows554 : Nat := (Nat.lor 0x280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000008001003000602002e000001404380681000240000100000000000000000000000000a0000000040000000009002802d000000000002 (Nat.shiftLeft 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 554. -/
noncomputable def allowed554 : List Nat := [0x40000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 554. -/
noncomputable def tree554 : ParitySearchTree := (.split 4 (.pack [4]) (.split 26 (.pack [7]) (.split 29 (.pack [9]) (.split 44 (.pack [12]) (.split 51 (.pack [0]) (.split 53 (.pack [0]) (.split 54 (.pack [14]) (.split 63 (.pack [16]) (.split 64 (.pack [17]) (.split 65 (.pack [18]) (.split 70 (.pack [15]) (.split 78 .done (.split 80 .done (.split 105 (.pack [4]) (.split 106 (.pack [5]) (.split 107 (.pack [4]) (.split 109 (.pack [6]) (.split 121 (.pack [10]) (.split 129 (.pack [2]) (.split 130 (.pack [3]) (.split 144 (.pack [8]) (.split 145 (.pack [13]) (.split 156 (.pack [11]) (.split 171 (.pack [13]) (.zero 1)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 554. -/
theorem checked554 : checkParitySearch 8 (fun q => (rows554 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed554.contains) tree554 0xffcff9bffbffffffffffb83f9fff3feeffdfffdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 555. -/
noncomputable def rows555 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000400000000000000080000010012003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 555. -/
noncomputable def allowed555 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 555. -/
noncomputable def tree555 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [3]) (.split 49 (.pack [4]) (.split 50 (.pack [5]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 .done (.split 92 (.pack [6]) (.split 119 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 555. -/
theorem checked555 : checkParitySearch 8 (fun q => (rows555 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed555.contains) tree555 0xffcff59fe9fffffffffff93ff3ffffe7ffffff4ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 556. -/
noncomputable def rows556 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000400000000000000080000010012003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000000080000010012003803f000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 556. -/
noncomputable def allowed556 : List Nat := [0x8000000000000,0x10000000000000,0x20000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 556. -/
noncomputable def tree556 : ParitySearchTree := (.split 2 (.pack [1]) (.split 48 (.pack [3]) (.split 49 (.pack [4]) (.split 50 (.pack [5]) (.split 51 .done (.split 52 .done (.split 53 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 77 (.pack [9]) (.split 80 .done (.split 92 (.pack [6]) (.split 119 (.pack [2]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 556. -/
theorem checked556 : checkParitySearch 8 (fun q => (rows556 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed556.contains) tree556 0xffcfee9fd9fffffffffff93ff3ffffebfffffecffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 557. -/
noncomputable def rows557 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000002002401801b00000000000000000010000010400000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000004000001400100000000000000000020020000000000000000000600780000000100100128004002022c0000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000020000003004800000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 557. -/
noncomputable def allowed557 : List Nat := [0x20000000000000000,0x400000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 557. -/
noncomputable def tree557 : ParitySearchTree := (.split 11 (.pack [4]) (.split 58 (.pack [8]) (.split 59 (.pack [9]) (.split 61 (.pack [7]) (.split 65 .done (.split 73 (.pack [11]) (.split 86 (.pack [0]) (.split 99 (.pack [1]) (.split 101 (.pack [1]) (.split 104 (.pack [3]) (.split 116 (.pack [5]) (.split 128 (.pack [6]) (.split 163 (.pack [10]) (.split 164 (.pack [10]) (.split 165 (.pack [6]) (.split 166 .done (.split 177 (.pack [12]) (.split 178 (.pack [7]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 557. -/
theorem checked557 : checkParitySearch 8 (fun q => (rows557 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed557.contains) tree557 0xffcfbfbfffbffffffff6ff57fd7fe3ffbffcdffdfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 558. -/
noncomputable def rows558 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000000180000000000000008000001001200000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000004000800a001400002000400400400190100024000000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000004000001400100000000000000000020020000000000000000000600780000000100100128004002022c0000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000020000003004800000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 558. -/
noncomputable def allowed558 : List Nat := [0x2000000000000000,0x20000000000000000,0x200000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 558. -/
noncomputable def tree558 : ParitySearchTree := (.split 11 (.pack [4]) (.split 58 (.pack [7]) (.split 59 (.pack [8]) (.split 61 .done (.split 65 .done (.split 73 (.pack [10]) (.split 86 (.pack [0]) (.split 99 (.pack [1]) (.split 101 (.pack [1]) (.split 104 (.pack [3]) (.split 116 (.pack [5]) (.split 128 (.pack [6]) (.split 163 (.pack [9]) (.split 164 (.pack [9]) (.split 165 .done (.split 166 .done (.split 177 (.pack [11]) (.split 178 .done (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 558. -/
theorem checked558 : checkParitySearch 8 (fun q => (rows558 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed558.contains) tree558 0xffcfbf9bfffffffffff6ff57fd7fe3ffdffcdffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 559. -/
noncomputable def rows559 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000e00000000000000000000000000007007e000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000008000000000000180000000000000040048006006c0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 559. -/
noncomputable def allowed559 : List Nat := [0x1000000000000,0x2000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 559. -/
noncomputable def tree559 : ParitySearchTree := (.split 33 (.pack [1]) (.split 34 (.pack [2]) (.split 35 (.pack [5]) (.split 36 (.pack [3]) (.split 37 (.pack [4]) (.split 38 (.pack [7]) (.split 48 .done (.split 49 .done (.split 50 (.pack [8]) (.split 165 (.pack [9]) (.split 166 (.pack [9]) (.split 167 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 559. -/
theorem checked559 : checkParitySearch 8 (fun q => (rows559 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed559.contains) tree559 0xffcf3f6ff61fffffdffffffbffffe4fffffffff7ff6ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 560. -/
noncomputable def rows560 : Nat := 0x2800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c002000000000000000000400400000000000000000000000006006000008006000001e00c000301b000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 560. -/
noncomputable def allowed560 : List Nat := [0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 560. -/
noncomputable def tree560 : ParitySearchTree := (.split 2 (.pack [1]) (.split 36 (.pack [6]) (.split 37 (.pack [7]) (.split 39 (.pack [8]) (.split 40 (.pack [9]) (.split 48 (.pack [10]) (.split 49 (.pack [11]) (.split 66 (.pack [13]) (.split 67 (.pack [14]) (.split 77 (.pack [12]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 105 (.pack [2]) (.split 106 (.pack [2]) (.split 119 (.pack [5]) (.split 141 (.pack [3]) (.split 142 (.pack [4]) (.split 153 (.pack [6]) (.split 154 (.pack [7]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 560. -/
theorem checked560 : checkParitySearch 8 (fun q => (rows560 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed560.contains) tree560 0xffceff6ffffffffffffff03fffffe4fc7ffb7ffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 561. -/
noncomputable def rows561 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000040028006006c10000000002401801900000208000080000000000000000000000000600000000800e000000e01e001b000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 561. -/
noncomputable def allowed561 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 561. -/
noncomputable def tree561 : ParitySearchTree := (.split 2 (.pack [2]) (.split 48 (.pack [8]) (.split 49 (.pack [9]) (.split 51 (.pack [10]) (.split 52 (.pack [10]) (.split 65 (.pack [11]) (.split 66 (.pack [12]) (.split 67 (.pack [13]) (.split 68 (.pack [14]) (.split 77 (.pack [11]) (.split 78 (.pack [1]) (.split 79 .done (.split 105 (.pack [4]) (.split 106 (.pack [4]) (.split 107 (.pack [3]) (.split 119 (.pack [5]) (.split 153 (.pack [6]) (.split 154 (.pack [7]) (.zero 0)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 561. -/
theorem checked561 : checkParitySearch 8 (fun q => (rows561 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed561.contains) tree561 0xffcefbeff7fffffffffff03fffffe4fdfffb7fbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 562. -/
noncomputable def rows562 : Nat := 0x400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000003000700600000000000000000000018018803f0000000000000000000000c000000002000000000080300360000000000010010000000000000000000000000000000002000000a004800000000000000000100000000000000000000004000000a000004002000800d007002f012000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 562. -/
noncomputable def allowed562 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 562. -/
noncomputable def tree562 : ParitySearchTree := (.split 0 (.pack [2]) (.split 1 .done (.split 2 (.pack [0]) (.split 3 (.pack [4]) (.split 4 (.pack [1]) (.split 5 (.pack [6]) (.split 15 (.pack [7]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 31 (.pack [9]) (.split 32 (.pack [10]) (.split 121 (.pack [1]) (.split 122 (.pack [8]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [9]) (.split 148 (.pack [11]) (.split 149 (.pack [11]) (.zero 3)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 562. -/
theorem checked562 : checkParitySearch 8 (fun q => (rows562 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed562.contains) tree562 0xffcdffdfffffffedff23fabfeffff7fefffeffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 563. -/
noncomputable def rows563 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000080060018000080008010013000a01a00120000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000002002400a00b4001000000000000001000001000000000000000000000000000000000800000280120000000000000000004000000000000000000000004000c00a00000200200000008078026012000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 563. -/
noncomputable def allowed563 : List Nat := [0x100000000000000000000,0x80000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 563. -/
noncomputable def tree563 : ParitySearchTree := (.split 21 (.pack [3]) (.split 24 (.pack [7]) (.split 37 (.pack [5]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 49 (.pack [9]) (.split 51 (.pack [11]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 68 (.pack [12]) (.split 80 .done (.split 91 .done (.split 107 (.pack [2]) (.split 127 (.pack [1]) (.split 128 (.pack [5]) (.split 141 (.pack [10]) (.split 142 (.pack [10]) (.split 155 (.pack [6]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 563. -/
theorem checked563 : checkParitySearch 8 (fun q => (rows563 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed563.contains) tree563 0xffcdffdfffffffbeffb7fafff9fffffefffeffffe4ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 564. -/
noncomputable def rows564 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000080060018000080008010013000a01a001200000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000400000300000000000000000000002002400000000000000000000000c00000000200000000008030036000000000001001000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000060040004008000c00e01f8000000030016020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 564. -/
noncomputable def allowed564 : List Nat := [0x80000000000000000000000,0x800000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 564. -/
noncomputable def tree564 : ParitySearchTree := (.split 21 (.pack [3]) (.split 24 (.pack [4]) (.split 37 (.pack [6]) (.split 39 (.pack [8]) (.split 40 (.pack [9]) (.split 49 (.pack [10]) (.split 51 (.pack [12]) (.split 64 (.pack [2]) (.split 65 (.pack [2]) (.split 68 (.pack [13]) (.split 80 (.pack [0]) (.split 91 .done (.split 107 .done (.split 127 (.pack [1]) (.split 128 (.pack [6]) (.split 141 (.pack [4]) (.split 142 (.pack [11]) (.split 155 (.pack [7]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 564. -/
theorem checked564 : checkParitySearch 8 (fun q => (rows564 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed564.contains) tree564 0xffcdffdfffffffa5ff87fafffffffffefffeffffd7ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 565. -/
noncomputable def rows565 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000080060018000080008010013000a01a001200000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000001000000c000000000000000000000080090000000000000000000000c000000002000000000080300360000000000010010000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 565. -/
noncomputable def allowed565 : List Nat := [0x100000000000000000000,0x80000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 565. -/
noncomputable def tree565 : ParitySearchTree := (.split 21 (.pack [3]) (.split 24 (.pack [4]) (.split 37 (.pack [6]) (.split 39 (.pack [8]) (.split 40 (.pack [9]) (.split 49 (.pack [10]) (.split 51 (.pack [12]) (.split 64 (.pack [1]) (.split 65 (.pack [1]) (.split 68 (.pack [13]) (.split 80 .done (.split 91 .done (.split 107 (.pack [2]) (.split 127 (.pack [0]) (.split 128 (.pack [6]) (.split 141 (.pack [4]) (.split 142 (.pack [11]) (.split 155 (.pack [7]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 565. -/
theorem checked565 : checkParitySearch 8 (fun q => (rows565 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed565.contains) tree565 0xffcdffdfffffff93ffe7fafff3fffffefffeffffcfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 566. -/
noncomputable def rows566 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000400800140140000000180000030034000402400000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000040000008000001c01f800000000002002400000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 566. -/
noncomputable def allowed566 : List Nat := [0x10000000000000000,0x20000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 566. -/
noncomputable def tree566 : ParitySearchTree := (.split 2 (.pack [5]) (.split 5 (.pack [2]) (.split 17 (.pack [4]) (.split 63 (.pack [5]) (.split 64 .done (.split 65 .done (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 78 (.pack [0]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 107 (.pack [5]) (.split 134 (.pack [6]) (.zero 3)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 566. -/
theorem checked566 : checkParitySearch 8 (fun q => (rows566 >>> (256*q)) &&& (2^256-1)) 0x28 (allowed566.contains) tree566 0xffcdff9fffffffffff9aff97fd7ffdffdffcffffffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 567. -/
noncomputable def rows567 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000c000000002000000000080300360000000000010010000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 567. -/
noncomputable def allowed567 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 567. -/
noncomputable def tree567 : ParitySearchTree := (.split 0 (.pack [1]) (.split 1 .done (.split 2 .done (.split 3 (.pack [3]) (.split 4 (.pack [0]) (.split 5 (.pack [4]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [8]) (.zero 2)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 567. -/
theorem checked567 : checkParitySearch 8 (fun q => (rows567 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed567.contains) tree567 0xffcdfefffdffffffff03fabfebfff7fdfffeffeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 568. -/
noncomputable def rows568 : Nat := 0xc000000000000000400000080090000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000004002200000d800008008001000201180360082000000000000000000000000004002000400c0018000080000010010002c00800120000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 568. -/
noncomputable def allowed568 : List Nat := [0x10000000000000,0x20000000000000000,0x100000000000000000000,0x800000000000000000000000000,0x200000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 568. -/
noncomputable def tree568 : ParitySearchTree := (.split 21 (.pack [1]) (.split 27 (.pack [8]) (.split 37 (.pack [4]) (.split 38 (.pack [5]) (.split 40 (.pack [6]) (.split 41 (.pack [7]) (.split 51 (.pack [10]) (.split 52 .done (.split 56 (.pack [9]) (.split 65 .done (.split 80 .done (.split 95 (.pack [0]) (.split 107 .done (.split 127 (.pack [5]) (.split 128 (.pack [4]) (.split 130 (.pack [7]) (.split 131 (.pack [6]) (.split 153 .done (.split 157 (.pack [6]) (.split 170 (.pack [2]) (.zero 3)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 568. -/
theorem checked568 : checkParitySearch 8 (fun q => (rows568 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed568.contains) tree568 0xffcdfefffdffffb7ffeffa7ffbffeffdfffeffefe7ffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 569. -/
noncomputable def rows569 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000004002200000d800008008001000201180360082000000000000000000000000004002000400c0018000080000010010002c00800120000000000000000000000000000000400000300000000000000000000002002400000000000000000000000c000000002000000000080300360000000000010010000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 569. -/
noncomputable def allowed569 : List Nat := [0x100000000000000000000,0x800000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 569. -/
noncomputable def tree569 : ParitySearchTree := (.split 21 (.pack [2]) (.split 27 (.pack [9]) (.split 37 (.pack [5]) (.split 38 (.pack [6]) (.split 40 (.pack [7]) (.split 41 (.pack [8]) (.split 51 (.pack [11]) (.split 52 (.pack [12]) (.split 56 (.pack [10]) (.split 65 (.pack [1]) (.split 80 .done (.split 95 (.pack [0]) (.split 107 .done (.split 127 (.pack [6]) (.split 128 (.pack [5]) (.split 130 (.pack [8]) (.split 131 (.pack [7]) (.split 153 (.pack [12]) (.split 157 (.pack [7]) (.split 170 (.pack [3]) (.zero 4)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 569. -/
theorem checked569 : checkParitySearch 8 (fun q => (rows569 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed569.contains) tree569 0xffcdfefffdffffb7ffa7fafffbfffffdfffeffefe7ff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 570. -/
noncomputable def rows570 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000002002001401400001001000200040260004024000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000004000a00c008000005001600b80870250090000040040000000000000000000000000004006000200c00140090000000000020014034

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 570. -/
noncomputable def allowed570 : List Nat := [0x4,0x80000000000000000000,0x40000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 570. -/
noncomputable def tree570 : ParitySearchTree := (.split 2 .done (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 14 (.pack [4]) (.split 16 (.pack [5]) (.split 29 (.pack [7]) (.split 76 (.pack [11]) (.split 79 .done (.split 90 .done (.split 92 (.pack [6]) (.split 106 .done (.split 107 (.pack [1]) (.split 117 (.pack [5]) (.split 133 (.pack [9]) (.split 134 (.pack [8]) (.split 146 (.pack [10]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 570. -/
theorem checked570 : checkParitySearch 8 (fun q => (rows570 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed570.contains) tree570 0xffcbffbfffffffdbffd3fd7fefffcfff7ffdffffd7ffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 571. -/
noncomputable def rows571 : Nat := 0x800000280000000000000000000004004800000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000002800700500000000000000000000014015003f0000000000000000000000a0000000040000000001002802d0000000000020020000000000000000000000000000000001000000c002400000000000000000080000000000000000000004000000c000002004000400c80a8037009000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 571. -/
noncomputable def allowed571 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 571. -/
noncomputable def tree571 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 (.pack [2]) (.split 2 .done (.split 3 (.pack [1]) (.split 4 (.pack [5]) (.split 5 (.pack [6]) (.split 16 (.pack [7]) (.split 18 (.pack [4]) (.split 20 (.pack [6]) (.split 30 (.pack [9]) (.split 32 (.pack [10]) (.split 120 (.pack [1]) (.split 122 (.pack [8]) (.split 132 (.pack [10]) (.split 133 (.pack [10]) (.split 134 (.pack [9]) (.split 147 (.pack [11]) (.split 149 (.pack [11]) (.zero 3)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 571. -/
theorem checked571 : checkParitySearch 8 (fun q => (rows571 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed571.contains) tree571 0xffcbffbfffffffdbff43fc7fefffefff7ffdffffd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 572. -/
noncomputable def rows572 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000a0000000040000000001002802d0000000000020020000000000000000000000a00000000a0000000002802802d000000000005005

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 572. -/
noncomputable def allowed572 : List Nat := [0x1,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 572. -/
noncomputable def tree572 : ParitySearchTree := (.split 0 .done (.split 2 .done (.split 12 (.pack [2]) (.split 14 (.pack [3]) (.split 60 (.pack [6]) (.split 62 (.pack [7]) (.split 63 (.pack [1]) (.split 65 (.pack [1]) (.split 75 (.pack [8]) (.split 77 (.pack [9]) (.split 87 (.pack [8]) (.split 89 (.pack [9]) (.split 129 (.pack [4]) (.split 131 (.pack [4]) (.split 165 (.pack [5]) (.split 167 (.pack [1]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 572. -/
theorem checked572 : checkParitySearch 8 (fun q => (rows572 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed572.contains) tree572 0xffcbffbfffffffb7ff83fc7ff7ffefff7ffdffffe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 573. -/
noncomputable def rows573 : Nat := 0x100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000038006000000c000000000000000001c01c80360000000000000000000000000000001000000c000000000000000000000080090000000000000000000000a0000000040000000001002802d000000000002002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 573. -/
noncomputable def allowed573 : List Nat := [0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 573. -/
noncomputable def tree573 : ParitySearchTree := (.split 1 (.pack [0]) (.split 2 .done (.split 4 (.pack [4]) (.split 5 (.pack [5]) (.split 15 (.pack [1]) (.split 18 (.pack [3]) (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 30 (.pack [6]) (.split 31 (.pack [7]) (.split 32 (.pack [8]) (.split 106 (.pack [1]) (.split 107 (.pack [1]) (.split 133 (.pack [6]) (.split 134 (.pack [6]) (.split 147 (.pack [10]) (.split 148 (.pack [11]) (.split 149 (.pack [9]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 573. -/
theorem checked573 : checkParitySearch 8 (fun q => (rows573 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed573.contains) tree573 0xffcbffbfffffff93ffc3fc7fffffefff7ffdffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 574. -/
noncomputable def rows574 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000030000000000000c00d800000000001801b0030

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 574. -/
noncomputable def allowed574 : List Nat := [0x20000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 574. -/
noncomputable def tree574 : ParitySearchTree := (.split 12 (.pack [2]) (.split 13 (.pack [3]) (.split 14 (.pack [4]) (.split 15 (.pack [0]) (.split 16 (.pack [1]) (.split 17 .done (.split 27 (.pack [6]) (.split 28 (.pack [7]) (.split 29 (.pack [8]) (.split 144 (.pack [10]) (.split 145 (.pack [11]) (.split 146 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 574. -/
theorem checked574 : checkParitySearch 8 (fun q => (rows574 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed574.contains) tree574 0xffcbffbfffffff81ffabfcfffbffffff7ffdffffffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 575. -/
noncomputable def rows575 : Nat := 0x3000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000040000008000001c01f800000000002002400000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c002400000000000000000080000000000000000000200a0018000000080014010010801403e200000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 575. -/
noncomputable def allowed575 : List Nat := [0x4,0x10000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 575. -/
noncomputable def tree575 : ParitySearchTree := (.split 2 .done (.split 5 (.pack [3]) (.split 17 (.pack [5]) (.split 63 (.pack [0]) (.split 64 .done (.split 65 (.pack [0]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 78 (.pack [1]) (.split 79 (.pack [2]) (.split 80 (.pack [3]) (.split 107 (.pack [0]) (.split 134 (.pack [6]) (.zero 4)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 575. -/
theorem checked575 : checkParitySearch 8 (fun q => (rows575 >>> (256*q)) &&& (2^256-1)) 0x11 (allowed575.contains) tree575 0xffcbff9fffffffffff977f4ffcfffeffeffcffffffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 576. -/
noncomputable def rows576 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000a0000000040000000001002802d0000000000020020000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 576. -/
noncomputable def allowed576 : List Nat := [0x1,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 576. -/
noncomputable def tree576 : ParitySearchTree := (.split 0 .done (.split 1 (.pack [1]) (.split 2 .done (.split 3 (.pack [0]) (.split 4 (.pack [3]) (.split 5 (.pack [4]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [8]) (.zero 2)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 576. -/
theorem checked576 : checkParitySearch 8 (fun q => (rows576 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed576.contains) tree576 0xffcbfdfffbffffffff03fc7fe7ffeffdfffdffdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 577. -/
noncomputable def rows577 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000040000008000001c01f8000000000020024000000000000000000000000000000080000010002003803f000000000004004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 577. -/
noncomputable def allowed577 : List Nat := [0x4,0x8000000000000000,0x10000000000000000,0x20000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 577. -/
noncomputable def tree577 : ParitySearchTree := (.split 2 .done (.split 14 (.pack [2]) (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 63 .done (.split 64 .done (.split 65 .done (.split 75 (.pack [7]) (.split 76 (.pack [8]) (.split 77 (.pack [9]) (.split 89 (.pack [9]) (.split 104 (.pack [1]) (.split 131 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 577. -/
theorem checked577 : checkParitySearch 8 (fun q => (rows577 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed577.contains) tree577 0xffc9febffdffffffff93ff3ffffffffcfffcffefffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 578. -/
noncomputable def rows578 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000040000008000001c01f8000000000020024000000000000000000000000000000080000010002003803f000000000004004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 578. -/
noncomputable def allowed578 : List Nat := [0x4,0x8000000000000000,0x10000000000000000,0x20000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 578. -/
noncomputable def tree578 : ParitySearchTree := (.split 2 .done (.split 14 (.pack [2]) (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 63 .done (.split 64 .done (.split 65 .done (.split 75 (.pack [7]) (.split 76 (.pack [8]) (.split 77 (.pack [9]) (.split 89 (.pack [9]) (.split 104 (.pack [1]) (.split 131 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 578. -/
theorem checked578 : checkParitySearch 8 (fun q => (rows578 >>> (256*q)) &&& (2^256-1)) 0x3 (allowed578.contains) tree578 0xffc9fddffbffffffff93ff3ffffffffd7ffcffdfffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 579. -/
noncomputable def rows579 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000004006000c00000000a00200140128040009000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000400000060000000000000000000002002400000000000000000000000300000000240000028000003c03b8000000000120104000000000000000000000060000000080000000002001801b0000000000040040000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000000800000600120000000000000000004000000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 579. -/
noncomputable def allowed579 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 579. -/
noncomputable def tree579 : ParitySearchTree := (.split 2 (.pack [0]) (.split 8 (.pack [2]) (.split 17 (.pack [5]) (.split 20 (.pack [6]) (.split 63 (.pack [3]) (.split 64 (.pack [3]) (.split 65 (.pack [11]) (.split 67 (.pack [12]) (.split 68 (.pack [13]) (.split 69 (.pack [10]) (.split 78 (.pack [9]) (.split 79 .done (.split 80 (.pack [0]) (.split 81 (.pack [1]) (.split 107 (.pack [9]) (.split 109 (.pack [12]) (.split 134 (.pack [7]) (.split 137 (.pack [8]) (.split 172 (.pack [13]) (.split 173 (.pack [12]) (.zero 4)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 579. -/
theorem checked579 : checkParitySearch 8 (fun q => (rows579 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed579.contains) tree579 0xffc7ff7ffffffffffeb3f2ffffffbffc7ffbfffffffcc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 580. -/
noncomputable def rows580 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000004005000a00000000c004001801300800120000000000000000000000000000004005600c000000004004c008000808300900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000280000000240000018000005c0578000000000120104000000000000000000000060000000080000000002001801b00000000000400400000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 580. -/
noncomputable def allowed580 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 580. -/
noncomputable def tree580 : ParitySearchTree := (.split 37 (.pack [5]) (.split 40 (.pack [7]) (.split 55 (.pack [11]) (.split 64 (.pack [1]) (.split 65 (.pack [12]) (.split 68 (.pack [13]) (.split 79 .done (.split 80 (.pack [0]) (.split 94 (.pack [2]) (.split 106 (.pack [2]) (.split 107 (.pack [9]) (.split 141 (.pack [3]) (.split 143 (.pack [4]) (.split 156 (.pack [6]) (.split 158 (.pack [8]) (.split 170 (.pack [2]) (.zero 10)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 580. -/
theorem checked580 : checkParitySearch 8 (fun q => (rows580 >>> (256*q)) &&& (2^256-1)) 0x604 (allowed580.contains) tree580 0xffc7ff7ffffffffffdd3f4ffffff7ffc7ffbfffffffd4 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 581. -/
noncomputable def rows581 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000004005000a00000000c004001801300800120000000000000000000000000000004006000c00000000a0020014012804000900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000004000000600000000000000000000020024000000000000000000000060000000080000000002001801b000000000004004000000000000000000000000000000000400000060090000000000000000002000000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 581. -/
noncomputable def allowed581 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 581. -/
noncomputable def tree581 : ParitySearchTree := (.split 37 (.pack [6]) (.split 40 (.pack [8]) (.split 55 (.pack [12]) (.split 64 (.pack [2]) (.split 65 (.pack [13]) (.split 68 (.pack [14]) (.split 79 .done (.split 80 (.pack [0]) (.split 94 (.pack [1]) (.split 106 (.pack [3]) (.split 107 (.pack [10]) (.split 141 (.pack [4]) (.split 143 (.pack [5]) (.split 156 (.pack [7]) (.split 158 (.pack [9]) (.split 170 (.pack [10]) (.zero 11)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 581. -/
theorem checked581 : checkParitySearch 8 (fun q => (rows581 >>> (256*q)) &&& (2^256-1)) 0x800 (allowed581.contains) tree581 0xffc7ff7ffffffffffcf3f6ffffff3ffc7ffbfffffffe4 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 582. -/
noncomputable def rows582 : Nat := (Nat.lor 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000001000000c0000000000000000000000800900000000000000000000006000000048000008000201d81e3000000000024020000000000000000000000000000000010000001802400000000000000000080000000000000000000000000060000000010000000002401801b00000000000080000000000000000000004000000c000002004000400c80a8037009000000001 (Nat.shiftLeft 0xa000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 582. -/
noncomputable def allowed582 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 582. -/
noncomputable def tree582 : ParitySearchTree := (.split 5 (.pack [5]) (.split 14 (.pack [6]) (.split 17 (.pack [7]) (.split 60 (.pack [10]) (.split 61 (.pack [11]) (.split 65 (.pack [12]) (.split 66 (.pack [13]) (.split 67 (.pack [14]) (.split 68 (.pack [15]) (.split 75 (.pack [16]) (.split 76 (.pack [17]) (.split 78 (.pack [1]) (.split 79 .done (.split 80 (.pack [0]) (.split 89 (.pack [2]) (.split 107 (.pack [4]) (.split 131 (.pack [8]) (.split 134 (.pack [9]) (.split 165 (.pack [12]) (.split 166 (.pack [12]) (.zero 3)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 582. -/
theorem checked582 : checkParitySearch 8 (fun q => (rows582 >>> (256*q)) &&& (2^256-1)) 0x9 (allowed582.contains) tree582 0xffc7fe5ffdffffffffdbf07fffffefff7ffbffefffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 583. -/
noncomputable def rows583 : Nat := (Nat.lor 0xc0000000000000004000000800900000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a0000000000000000000001001200000000000000000000006000000048000008000201d81e3000000000024020000000000000000000000000000000010000001802400000000000000000080000000000000000000000000060000000010000000002401801b0000000000008 (Nat.shiftLeft 0xa00000000000000080000010012000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 583. -/
noncomputable def allowed583 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 583. -/
noncomputable def tree583 : ParitySearchTree := (.split 5 (.pack [4]) (.split 14 (.pack [5]) (.split 17 (.pack [6]) (.split 60 (.pack [9]) (.split 61 (.pack [10]) (.split 65 (.pack [11]) (.split 66 (.pack [12]) (.split 67 (.pack [13]) (.split 68 (.pack [14]) (.split 75 (.pack [15]) (.split 76 (.pack [16]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 .done (.split 89 (.pack [1]) (.split 107 (.pack [3]) (.split 131 (.pack [7]) (.split 134 (.pack [8]) (.split 165 (.pack [11]) (.split 166 (.pack [11]) (.zero 2)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 583. -/
theorem checked583 : checkParitySearch 8 (fun q => (rows583 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed583.contains) tree583 0xffc7fe5ffdffffffffb7f0bffffff7ff7ffbffefffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 584. -/
noncomputable def rows584 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000040004000000c000080004010012803103b0048000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000008000001c01f8000000000020024000000000000000000000060000000080000000002001801b00000000000400400000000000000000000000060000000010000000002401801b000000000000800000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 584. -/
noncomputable def allowed584 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 584. -/
noncomputable def tree584 : ParitySearchTree := (.split 2 (.pack [0]) (.split 5 (.pack [4]) (.split 17 (.pack [5]) (.split 63 (.pack [2]) (.split 64 (.pack [2]) (.split 65 (.pack [8]) (.split 66 (.pack [9]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 78 (.pack [1]) (.split 79 .done (.split 80 (.pack [0]) (.split 107 (.pack [6]) (.split 134 (.pack [7]) (.zero 3)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 584. -/
theorem checked584 : checkParitySearch 8 (fun q => (rows584 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed584.contains) tree584 0xffc7fe5ffdffffffff93f0ffffffffff7ffbffefffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 585. -/
noncomputable def rows585 : Nat := (Nat.lor 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a0000000000000000000001001200000000000000000000006000000048000008000201d81e3000000000024020000000000000000000000000000000010000001802400000000000000000080000000000000000000000000050000000020000000004801401680000000000100000000000000000000004000000a000004002000800d007002f012000000002 (Nat.shiftLeft 0xa000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 585. -/
noncomputable def allowed585 : List Nat := [0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 585. -/
noncomputable def tree585 : ParitySearchTree := (.split 5 (.pack [5]) (.split 14 (.pack [6]) (.split 17 (.pack [7]) (.split 60 (.pack [10]) (.split 61 (.pack [11]) (.split 65 (.pack [12]) (.split 66 (.pack [13]) (.split 67 (.pack [14]) (.split 68 (.pack [15]) (.split 75 (.pack [16]) (.split 76 (.pack [17]) (.split 78 (.pack [0]) (.split 79 (.pack [1]) (.split 80 .done (.split 89 (.pack [2]) (.split 107 (.pack [4]) (.split 131 (.pack [8]) (.split 134 (.pack [9]) (.split 165 (.pack [12]) (.split 166 (.pack [12]) (.zero 3)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 585. -/
theorem checked585 : checkParitySearch 8 (fun q => (rows585 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed585.contains) tree585 0xffc7fd3ffbffffffffb7f0bffffff7fefffbffdfffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 586. -/
noncomputable def rows586 : Nat := (Nat.lor 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000012000002400081f81c700000000000900800000000000000000000000030000000040000000009000c00d800000000002000000000000000000000040028006006c1000000000240180190000020800008 (Nat.shiftLeft 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 586. -/
noncomputable def allowed586 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 586. -/
noncomputable def tree586 : ParitySearchTree := (.split 3 (.pack [5]) (.split 12 (.pack [6]) (.split 15 (.pack [7]) (.split 60 (.pack [10]) (.split 61 (.pack [11]) (.split 62 (.pack [12]) (.split 66 (.pack [13]) (.split 67 (.pack [14]) (.split 68 (.pack [15]) (.split 75 (.pack [16]) (.split 76 (.pack [17]) (.split 77 (.pack [18]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 (.pack [1]) (.split 87 (.pack [16]) (.split 102 (.pack [3]) (.split 105 (.pack [4]) (.split 129 (.pack [8]) (.split 132 (.pack [9]) (.zero 2)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 586. -/
theorem checked586 : checkParitySearch 8 (fun q => (rows586 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed586.contains) tree586 0xffc7fbfff7ffffffff6ff13fffffc7fdfffbffbfffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 587. -/
noncomputable def rows587 : Nat := (Nat.lor 0x300000000000000010000002002400000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000000030000000040000000009000c00d800000000002000000000000000000000040018006006c200000000048014014800002080001000000000000000000000040028006006c1000000000240180190000020800008 (Nat.shiftLeft 0x1800000000000000400000080090000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000018000000000000004000000800900000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 587. -/
noncomputable def allowed587 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 587. -/
noncomputable def tree587 : ParitySearchTree := (.split 4 (.pack [6]) (.split 23 (.pack [7]) (.split 29 (.pack [10]) (.split 51 (.pack [2]) (.split 54 (.pack [15]) (.split 56 (.pack [16]) (.split 66 (.pack [17]) (.split 68 (.pack [18]) (.split 79 .done (.split 82 (.pack [3]) (.split 121 (.pack [11]) (.split 126 (.pack [4]) (.split 127 (.pack [5]) (.split 129 (.pack [13]) (.split 130 (.pack [12]) (.split 141 (.pack [8]) (.split 142 (.pack [9]) (.split 155 (.pack [14]) (.split 156 (.pack [12]) (.split 170 (.pack [0]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 587. -/
theorem checked587 : checkParitySearch 8 (fun q => (rows587 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed587.contains) tree587 0xffc7fbfff7ffffffff27f1bfffffd7fdfffbffbfffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 588. -/
noncomputable def rows588 : Nat := (Nat.lor 0x60000000000000010000002002400000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000060000000080000010012001801b0000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000080000060012000000000000000000400000000000000000000030000a000240008028000402e03a80120000001201000000000000000000000004200c006c0000200080000058022012020800000001 (Nat.shiftLeft 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 588. -/
noncomputable def allowed588 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 588. -/
noncomputable def tree588 : ParitySearchTree := (.split 8 (.pack [3]) (.split 17 (.pack [6]) (.split 20 (.pack [7]) (.split 49 (.pack [11]) (.split 52 (.pack [12]) (.split 63 (.pack [13]) (.split 65 (.pack [15]) (.split 67 (.pack [16]) (.split 68 (.pack [17]) (.split 69 (.pack [14]) (.split 77 (.pack [15]) (.split 78 (.pack [0]) (.split 79 .done (.split 81 (.pack [2]) (.split 90 (.pack [13]) (.split 107 (.pack [4]) (.split 109 (.pack [16]) (.split 119 (.pack [5]) (.split 134 (.pack [9]) (.split 137 (.pack [10]) (.split 153 (.pack [8]) (.split 155 (.pack [13]) (.split 172 (.pack [17]) (.split 173 (.pack [16]) (.zero 1)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 588. -/
theorem checked588 : checkParitySearch 8 (fun q => (rows588 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed588.contains) tree588 0xffc7fbfff7fffffffefbf27fffffaffdfffbffbffffc9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 589. -/
noncomputable def rows589 : Nat := (Nat.lor 0xc00000000000000040000008009000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000004000001400100000000000000000020020000000000000000000004400a006c00004000400000980210090208000000020000000000000000000004200c006c0000200080000058022012020800000001 (Nat.shiftLeft 0xa00000000000000080000010012000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 589. -/
noncomputable def allowed589 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 589. -/
noncomputable def tree589 : ParitySearchTree := (.split 1 (.pack [2]) (.split 35 (.pack [7]) (.split 41 (.pack [12]) (.split 48 (.pack [9]) (.split 51 (.pack [11]) (.split 60 (.pack [13]) (.split 65 (.pack [14]) (.split 75 (.pack [15]) (.split 76 (.pack [16]) (.split 79 .done (.split 102 (.pack [2]) (.split 118 (.pack [6]) (.split 138 (.pack [3]) (.split 139 (.pack [9]) (.split 141 (.pack [4]) (.split 142 (.pack [5]) (.split 153 (.pack [8]) (.split 155 (.pack [0]) (.split 166 (.pack [10]) (.split 170 (.pack [0]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 589. -/
theorem checked589 : checkParitySearch 8 (fun q => (rows589 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed589.contains) tree589 0xffc7fbfff7fffffffedff23fffffa7fdfffbffbffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 590. -/
noncomputable def rows590 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000060000000080000010012001801b000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000400000060000000000000000000002002400000000000000000000000300000000240000028000003c03b80000000001201040000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000000800000600120000000000000000004000000000000000000000040028006006c100000000024018019000002080000800000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 590. -/
noncomputable def allowed590 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 590. -/
noncomputable def tree590 : ParitySearchTree := (.split 2 (.pack [0]) (.split 8 (.pack [3]) (.split 17 (.pack [5]) (.split 20 (.pack [6]) (.split 63 (.pack [10]) (.split 64 (.pack [11]) (.split 65 (.pack [13]) (.split 67 (.pack [14]) (.split 68 (.pack [15]) (.split 69 (.pack [12]) (.split 78 (.pack [1]) (.split 79 .done (.split 80 (.pack [0]) (.split 81 (.pack [2]) (.split 107 (.pack [9]) (.split 109 (.pack [14]) (.split 134 (.pack [7]) (.split 137 (.pack [8]) (.split 172 (.pack [15]) (.split 173 (.pack [14]) (.zero 4)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 590. -/
theorem checked590 : checkParitySearch 8 (fun q => (rows590 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed590.contains) tree590 0xffc7fbfff7fffffffeb3f2ffffffbffdfffbffbffffcc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 591. -/
noncomputable def rows591 : Nat := (Nat.lor 0x6000000000000001000000200240000000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000040000014001000000000000000000200200000000000000000000044000006c0002000e404005480311dc0208000000100000000000000000000004400a006c0000400040000098021009020800000002 (Nat.shiftLeft 0xa000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 591. -/
noncomputable def allowed591 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 591. -/
noncomputable def tree591 : ParitySearchTree := (.split 1 (.pack [2]) (.split 35 (.pack [7]) (.split 41 (.pack [12]) (.split 48 (.pack [9]) (.split 51 (.pack [11]) (.split 60 (.pack [13]) (.split 65 (.pack [15]) (.split 75 (.pack [16]) (.split 76 (.pack [17]) (.split 79 .done (.split 102 (.pack [2]) (.split 118 (.pack [6]) (.split 138 (.pack [3]) (.split 139 (.pack [9]) (.split 141 (.pack [4]) (.split 142 (.pack [5]) (.split 153 (.pack [8]) (.split 155 (.pack [14]) (.split 166 (.pack [10]) (.split 170 (.pack [1]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 591. -/
theorem checked591 : checkParitySearch 8 (fun q => (rows591 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed591.contains) tree591 0xffc7fbfff7fffffffdf7f4bfffff77fdfffbffbffffd2 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 592. -/
noncomputable def rows592 : Nat := (Nat.lor 0x1800000000000000400000080090000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000040018006006c2000000000480140148000020800010000000000000000000002c0028006086c1004000000640500190000020840040 (Nat.shiftLeft 0x180000000000000040000008009000000000000000000000000000000000000030000000000000001000000200240000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 592. -/
noncomputable def allowed592 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 592. -/
noncomputable def tree592 : ParitySearchTree := (.split 4 (.pack [5]) (.split 23 (.pack [6]) (.split 29 (.pack [9]) (.split 51 (.pack [13]) (.split 54 (.pack [14]) (.split 56 (.pack [15]) (.split 66 (.pack [16]) (.split 68 (.pack [17]) (.split 79 .done (.split 82 (.pack [2]) (.split 121 (.pack [10]) (.split 126 (.pack [3]) (.split 127 (.pack [4]) (.split 129 (.pack [12]) (.split 130 (.pack [11]) (.split 141 (.pack [7]) (.split 142 (.pack [8]) (.split 155 (.pack [13]) (.split 156 (.pack [11]) (.split 170 (.pack [0]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 592. -/
theorem checked592 : checkParitySearch 8 (fun q => (rows592 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed592.contains) tree592 0xffc7fbfff7fffffffdd3f4ffffff7ffdfffbffbffffd4 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 593. -/
noncomputable def rows593 : Nat := (Nat.lor 0x30000000000000001000000200240000000000000000000000000000000000000000060000000080000010012001801b0000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200000000000000000000000000000000001000000500240000000000000000008000000000000000000000040018006006c2000000000480140148000020800010000000000000000000002c0028006086c1004000000640500190000020840040 (Nat.shiftLeft 0x1800000000000000400000080090000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000018000000000000004000000800900000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 593. -/
noncomputable def allowed593 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 593. -/
noncomputable def tree593 : ParitySearchTree := (.split 4 (.pack [7]) (.split 23 (.pack [8]) (.split 29 (.pack [11]) (.split 51 (.pack [14]) (.split 54 (.pack [15]) (.split 56 (.pack [16]) (.split 66 (.pack [17]) (.split 68 (.pack [18]) (.split 79 .done (.split 82 (.pack [2]) (.split 121 (.pack [12]) (.split 126 (.pack [3]) (.split 127 (.pack [4]) (.split 129 (.pack [5]) (.split 130 (.pack [6]) (.split 141 (.pack [9]) (.split 142 (.pack [10]) (.split 155 (.pack [0]) (.split 156 (.pack [13]) (.split 170 (.pack [0]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 593. -/
theorem checked593 : checkParitySearch 8 (fun q => (rows593 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed593.contains) tree593 0xffc7fbfff7fffffffdbff43fffff67fdfffbffbffffd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 594. -/
noncomputable def rows594 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000003000000000000e006001c01380d80000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000060000000080000010012001801b0000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000040010002006000c0c004001801300800320200048000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000000400000060090000000000000000002000000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 594. -/
noncomputable def allowed594 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 594. -/
noncomputable def tree594 : ParitySearchTree := (.split 51 (.pack [7]) (.split 52 (.pack [8]) (.split 54 (.pack [10]) (.split 55 (.pack [11]) (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [12]) (.split 68 (.pack [13]) (.split 78 (.pack [3]) (.split 79 .done (.split 80 (.pack [0]) (.split 93 (.pack [1]) (.split 94 (.pack [1]) (.split 105 (.pack [2]) (.split 106 (.pack [2]) (.split 107 (.pack [6]) (.split 156 (.pack [4]) (.split 157 (.pack [5]) (.zero 9)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 594. -/
theorem checked594 : checkParitySearch 8 (fun q => (rows594 >>> (256*q)) &&& (2^256-1)) 0x208 (allowed594.contains) tree594 0xffc7fbfff7fffffffcf3f6ffffff3ffdfffbffbffffe4 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 595. -/
noncomputable def rows595 : Nat := (Nat.lor 0xc0000000000000004000000800900000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000040000014001000000000000000000200200000000000000000000000030000000040000000009000c00d80000000000200000000000000000000004400a006c00004000400000980210090208000000020000000000000000000004200c006c0000200080000058022012020800000001 (Nat.shiftLeft 0xa00000000000000080000010012000000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 595. -/
noncomputable def allowed595 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 595. -/
noncomputable def tree595 : ParitySearchTree := (.split 1 (.pack [3]) (.split 35 (.pack [8]) (.split 41 (.pack [12]) (.split 48 (.pack [10]) (.split 51 (.pack [2]) (.split 60 (.pack [13]) (.split 65 (.pack [14]) (.split 75 (.pack [15]) (.split 76 (.pack [16]) (.split 79 .done (.split 102 (.pack [3]) (.split 118 (.pack [7]) (.split 138 (.pack [4]) (.split 139 (.pack [10]) (.split 141 (.pack [5]) (.split 142 (.pack [6]) (.split 153 (.pack [9]) (.split 155 (.pack [0]) (.split 166 (.pack [11]) (.split 170 (.pack [0]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 595. -/
theorem checked595 : checkParitySearch 8 (fun q => (rows595 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed595.contains) tree595 0xffc7fbfff7fffffffb7ff83ffffee7fdfffbffbffffe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 596. -/
noncomputable def rows596 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000600000000000000ec00001d81e30000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000004200c000c000020088000015810200a03b800000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 596. -/
noncomputable def allowed596 : List Nat := [0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 596. -/
noncomputable def tree596 : ParitySearchTree := (.split 60 (.pack [6]) (.split 61 (.pack [7]) (.split 65 (.pack [9]) (.split 66 (.pack [10]) (.split 67 (.pack [11]) (.split 68 (.pack [12]) (.split 75 (.pack [13]) (.split 76 (.pack [14]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 (.pack [0]) (.split 102 (.pack [1]) (.split 103 (.pack [2]) (.split 105 (.pack [4]) (.split 106 (.pack [5]) (.split 107 (.pack [3]) (.split 165 (.pack [9]) (.split 166 (.pack [9]) (.zero 8)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 596. -/
theorem checked596 : checkParitySearch 8 (fun q => (rows596 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed596.contains) tree596 0xffc7fadff5fffffffffff03fffffe7fefffbffaffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 597. -/
noncomputable def rows597 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000600000000000000ec00001d81e30000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000004200a000c00004006800000400e201103b800000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 597. -/
noncomputable def allowed597 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 597. -/
noncomputable def tree597 : ParitySearchTree := (.split 60 (.pack [6]) (.split 61 (.pack [7]) (.split 65 (.pack [9]) (.split 66 (.pack [10]) (.split 67 (.pack [11]) (.split 68 (.pack [12]) (.split 75 (.pack [13]) (.split 76 (.pack [14]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 .done (.split 102 (.pack [1]) (.split 103 (.pack [2]) (.split 105 (.pack [4]) (.split 106 (.pack [5]) (.split 107 (.pack [3]) (.split 165 (.pack [9]) (.split 166 (.pack [9]) (.zero 8)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 597. -/
theorem checked597 : checkParitySearch 8 (fun q => (rows597 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed597.contains) tree597 0xffc7f9bff3fffffffffff03fffffe7ff7ffbff9ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 598. -/
noncomputable def rows598 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000000000000000000038000007007e0000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 598. -/
noncomputable def allowed598 : List Nat := [0x1000000000000000,0x2000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 598. -/
noncomputable def tree598 : ParitySearchTree := (.split 57 (.pack [2]) (.split 58 (.pack [3]) (.split 59 (.pack [4]) (.split 60 .done (.split 61 .done (.split 62 (.pack [6]) (.split 72 (.pack [7]) (.split 73 (.pack [8]) (.split 74 (.pack [9]) (.split 99 (.pack [1]) (.split 100 (.pack [0]) (.split 101 (.pack [0]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 598. -/
theorem checked598 : checkParitySearch 8 (fun q => (rows598 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed598.contains) tree598 0xffc63feff71fffffdffffffbffffe7ffcfff7fffff6ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 599. -/
noncomputable def rows599 : Nat := (Nat.lor 0x30000000000000001000000200240000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c0020000000000000000004004000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000400000300090000000000000000002000000000000000000000004001400a00b41000200400200148130000010400008 (Nat.shiftLeft 0x18000000000000004000000800900000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 599. -/
noncomputable def allowed599 : List Nat := [0x8000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 599. -/
noncomputable def tree599 : ParitySearchTree := (.split 3 (.pack [5]) (.split 22 (.pack [6]) (.split 28 (.pack [9]) (.split 52 (.pack [13]) (.split 53 (.pack [12]) (.split 56 (.pack [14]) (.split 63 .done (.split 66 (.pack [15]) (.split 68 (.pack [16]) (.split 81 (.pack [15]) (.split 94 (.pack [13]) (.split 105 (.pack [4]) (.split 120 (.pack [10]) (.split 126 (.pack [1]) (.split 128 (.pack [2]) (.split 129 (.pack [11]) (.split 131 (.pack [3]) (.split 141 (.pack [7]) (.split 143 (.pack [8]) (.split 154 (.pack [12]) (.split 156 (.pack [13]) (.split 170 .done (.zero 0)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 599. -/
theorem checked599 : checkParitySearch 8 (fun q => (rows599 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed599.contains) tree599 0xffc3fd7ffbffffffff6ff5bfebffeffffff9ffdfffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 600. -/
noncomputable def rows600 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e00000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000000000000180000000200000040048006006c0000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 600. -/
noncomputable def allowed600 : List Nat := [0x2000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 600. -/
noncomputable def tree600 : ParitySearchTree := (.split 57 (.pack [5]) (.split 58 (.pack [6]) (.split 59 (.pack [7]) (.split 60 (.pack [4]) (.split 61 .done (.split 62 (.pack [3]) (.split 72 (.pack [9]) (.split 73 (.pack [10]) (.split 74 (.pack [11]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 8)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 600. -/
theorem checked600 : checkParitySearch 8 (fun q => (rows600 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed600.contains) tree600 0xffb83fbbff5ffdffffffffffffffe7ff9ffb7ff3ffeff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 601. -/
noncomputable def rows601 : Nat := 0x500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000030000000040000000000000c00d800000000002002400000000000000000000030000000030000000000000c00d800000000001801b0000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c00240000000000000000008000000000000000000000000060000000080000000012001801b000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 601. -/
noncomputable def allowed601 : List Nat := [0x1,0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 601. -/
noncomputable def tree601 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 3 (.pack [1]) (.split 4 (.pack [2]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 63 (.pack [0]) (.split 64 (.pack [0]) (.split 66 (.pack [10]) (.split 67 (.pack [11]) (.split 78 (.pack [1]) (.split 79 (.pack [2]) (.split 132 (.pack [7]) (.split 133 (.pack [8]) (.split 168 (.pack [9]) (.split 169 (.pack [4]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 601. -/
theorem checked601 : checkParitySearch 8 (fun q => (rows601 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed601.contains) tree601 0xffb7ff6dffdfffffff03fe3fffffdffff9fbfffefffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 602. -/
noncomputable def rows602 : Nat := 0x3000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000c00180180030000000000000000006006000d800000000000000000000000000000020000004000001c01f800000000001001200000000000000000000000000000004000001400100000000000000000020020000000000000000000000005000a000020004000004001d014002d0000000100000000000000000000000000a00a000004004000000100b800502d000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 602. -/
noncomputable def allowed602 : List Nat := [0x10000,0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 602. -/
noncomputable def tree602 : ParitySearchTree := (.split 1 (.pack [2]) (.split 4 (.pack [4]) (.split 16 .done (.split 63 (.pack [8]) (.split 64 (.pack [6]) (.split 65 (.pack [9]) (.split 66 (.pack [10]) (.split 67 (.pack [7]) (.split 68 (.pack [1]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 106 (.pack [0]) (.split 133 (.pack [5]) (.zero 3)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 602. -/
theorem checked602 : checkParitySearch 8 (fun q => (rows602 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed602.contains) tree602 0xffaffffffffffde5fb5ff4bf7ffffffd7fffffff17fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 603. -/
noncomputable def rows603 : Nat := 0x28000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000002000000300000000000000000000010012000000000000000000000000030006000040008000008001e00c001b00000002000000000000000000000000006006040008000000001e00c000301b000020020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 603. -/
noncomputable def allowed603 : List Nat := [0x40000000000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 603. -/
noncomputable def tree603 : ParitySearchTree := (.split 5 (.pack [2]) (.split 17 (.pack [5]) (.split 36 (.pack [6]) (.split 37 (.pack [7]) (.split 39 (.pack [8]) (.split 40 (.pack [9]) (.split 48 (.pack [11]) (.split 49 (.pack [12]) (.split 66 (.pack [14]) (.split 67 (.pack [15]) (.split 77 (.pack [13]) (.split 78 .done (.split 79 .done (.split 80 .done (.split 119 (.pack [4]) (.split 134 (.pack [10]) (.split 141 (.pack [3]) (.split 142 (.pack [1]) (.split 153 (.pack [6]) (.split 154 (.pack [7]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 603. -/
theorem checked603 : checkParitySearch 8 (fun q => (rows603 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed603.contains) tree603 0xff8ffffffffffffdbfdff07fff7ff7fc7ffffffff9ff9 0 1 = true := by decide +kernel

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

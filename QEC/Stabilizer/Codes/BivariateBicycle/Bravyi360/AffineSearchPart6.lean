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
/-- Packed parity neighborhoods for affine fiber 604. -/
noncomputable def rows604 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 604. -/
noncomputable def allowed604 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 604. -/
noncomputable def tree604 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 .done (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 604. -/
theorem checked604 : checkParitySearch 8 (fun q => (rows604 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed604.contains) tree604 0xff8ffedffdffffffb7ff703fffefffff7fffffefff3ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 605. -/
noncomputable def rows605 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000c00c0000080080008008002800100900000000400080400000000000000000000000060000000010000000002401801b0000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 605. -/
noncomputable def allowed605 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 605. -/
noncomputable def tree605 : ParitySearchTree := (.split 63 (.pack [1]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 .done (.split 105 (.pack [3]) (.split 106 (.pack [4]) (.split 107 (.pack [2]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 605. -/
theorem checked605 : checkParitySearch 8 (fun q => (rows605 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed605.contains) tree605 0xff8ffedffdfffffdbffbf03fff7fffff7fffffeff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 606. -/
noncomputable def rows606 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000000c00000000c000001801b003003600000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 606. -/
noncomputable def allowed606 : List Nat := [0x10000000000000,0x20000000000000,0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 606. -/
noncomputable def tree606 : ParitySearchTree := (.split 37 (.pack [3]) (.split 38 (.pack [4]) (.split 40 (.pack [5]) (.split 41 (.pack [6]) (.split 52 .done (.split 53 .done (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 79 .done (.split 80 .done (.split 106 (.pack [0]) (.split 107 (.pack [0]) (.split 142 (.pack [1]) (.split 143 (.pack [2]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 606. -/
theorem checked606 : checkParitySearch 8 (fun q => (rows606 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed606.contains) tree606 0xff8ffedffdffffedffdff03ffbffffff7fffffefcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 607. -/
noncomputable def rows607 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000000a0000000040000008009002802d00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 607. -/
noncomputable def allowed607 : List Nat := [0x40000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 607. -/
noncomputable def tree607 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 (.pack [3]) (.split 80 .done (.split 105 (.pack [1]) (.split 106 (.pack [2]) (.split 107 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 607. -/
theorem checked607 : checkParitySearch 8 (fun q => (rows607 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed607.contains) tree607 0xff8ffdbffbffffffb7ff703fffeffffeffffffdfff3ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 608. -/
noncomputable def rows608 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000000a0000000040000008009002802d00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000a0000000040000000009002802d000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 608. -/
noncomputable def allowed608 : List Nat := [0x40000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 608. -/
noncomputable def tree608 : ParitySearchTree := (.split 63 (.pack [0]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 (.pack [4]) (.split 80 .done (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 608. -/
theorem checked608 : checkParitySearch 8 (fun q => (rows608 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed608.contains) tree608 0xff8ffdbffbfffffdbffbf03fff7ffffeffffffdff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 609. -/
noncomputable def rows609 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 609. -/
noncomputable def allowed609 : List Nat := [0x40000000000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 609. -/
noncomputable def tree609 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 .done (.split 80 (.pack [3]) (.split 105 (.pack [1]) (.split 106 (.pack [2]) (.split 107 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 609. -/
theorem checked609 : checkParitySearch 8 (fun q => (rows609 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed609.contains) tree609 0xff8ffb7ff7ffffffb7ff703fffeffffdffffffbfff3ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 610. -/
noncomputable def rows610 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000060000000080000000012001801b000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 610. -/
noncomputable def allowed610 : List Nat := [0x40000000000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 610. -/
noncomputable def tree610 : ParitySearchTree := (.split 63 (.pack [0]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 .done (.split 80 (.pack [4]) (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 610. -/
theorem checked610 : checkParitySearch 8 (fun q => (rows610 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed610.contains) tree610 0xff8ffb7ff7fffffdbffbf03fff7ffffdffffffbff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 611. -/
noncomputable def rows611 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000000a0000000040000008009002802d00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 611. -/
noncomputable def allowed611 : List Nat := [0x40000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 611. -/
noncomputable def tree611 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 (.pack [3]) (.split 80 .done (.split 105 (.pack [1]) (.split 106 (.pack [2]) (.split 107 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 611. -/
theorem checked611 : checkParitySearch 8 (fun q => (rows611 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed611.contains) tree611 0xff8ff4bfebfffffffffff03fffffffe6ffffff5ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 612. -/
noncomputable def rows612 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 612. -/
noncomputable def allowed612 : List Nat := [0x40000000000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 612. -/
noncomputable def tree612 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 .done (.split 80 (.pack [3]) (.split 105 (.pack [1]) (.split 106 (.pack [2]) (.split 107 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 612. -/
theorem checked612 : checkParitySearch 8 (fun q => (rows612 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed612.contains) tree612 0xff8ff27fe7fffffffffff03fffffffe5ffffff3ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 613. -/
noncomputable def rows613 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 613. -/
noncomputable def allowed613 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 613. -/
noncomputable def tree613 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 .done (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 613. -/
theorem checked613 : checkParitySearch 8 (fun q => (rows613 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed613.contains) tree613 0xff8fb6df7dfffffffffff03fffffff3f7ffffbeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 614. -/
noncomputable def rows614 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000000a0000000040000008009002802d00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 614. -/
noncomputable def allowed614 : List Nat := [0x40000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 614. -/
noncomputable def tree614 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 (.pack [3]) (.split 80 .done (.split 105 (.pack [1]) (.split 106 (.pack [2]) (.split 107 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 614. -/
theorem checked614 : checkParitySearch 8 (fun q => (rows614 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed614.contains) tree614 0xff8fb5bf7bfffffffffff03fffffff3efffffbdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 615. -/
noncomputable def rows615 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 615. -/
noncomputable def allowed615 : List Nat := [0x40000000000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 615. -/
noncomputable def tree615 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [5]) (.split 65 (.pack [6]) (.split 66 (.pack [8]) (.split 67 (.pack [9]) (.split 68 (.pack [10]) (.split 78 .done (.split 79 .done (.split 80 (.pack [3]) (.split 105 (.pack [1]) (.split 106 (.pack [2]) (.split 107 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 615. -/
theorem checked615 : checkParitySearch 8 (fun q => (rows615 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed615.contains) tree615 0xff8fb37f77fffffffffff03fffffff3dfffffbbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 616. -/
noncomputable def rows616 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000700000000000000000000000000003803f0000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 616. -/
noncomputable def allowed616 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 616. -/
noncomputable def tree616 : ParitySearchTree := (.split 0 (.pack [0]) (.split 1 .done (.split 2 .done (.split 3 (.pack [2]) (.split 4 (.pack [3]) (.split 5 (.pack [4]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [8]) (.zero 1)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 616. -/
theorem checked616 : checkParitySearch 8 (fun q => (rows616 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed616.contains) tree616 0xff8dfefffdffffffff03f3bfe7fff7fffffeffeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 617. -/
noncomputable def rows617 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f80000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 617. -/
noncomputable def allowed617 : List Nat := [0x80000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 617. -/
noncomputable def tree617 : ParitySearchTree := (.split 63 (.pack [4]) (.split 64 (.pack [0]) (.split 65 (.pack [0]) (.split 66 (.pack [6]) (.split 67 (.pack [7]) (.split 68 (.pack [8]) (.split 78 (.pack [0]) (.split 79 .done (.split 80 .done (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 617. -/
theorem checked617 : checkParitySearch 8 (fun q => (rows617 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed617.contains) tree617 0xff8dbedbfdfffffffffff03ffffff9ff7fffdfeffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 618. -/
noncomputable def rows618 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f80000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000000a0000000040000008009002802d00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000a0000000040000000009002802d000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 618. -/
noncomputable def allowed618 : List Nat := [0x40000000000000000000,0x100000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 618. -/
noncomputable def tree618 : ParitySearchTree := (.split 63 (.pack [5]) (.split 64 (.pack [4]) (.split 65 (.pack [0]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 78 .done (.split 79 (.pack [4]) (.split 80 .done (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 618. -/
theorem checked618 : checkParitySearch 8 (fun q => (rows618 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed618.contains) tree618 0xff8dbdbbfbfffffffffff03ffffff9feffffdfdffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 619. -/
noncomputable def rows619 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000e000001c01f80000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000000060000000080000010012001801b00000000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000060000000080000000012001801b000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 619. -/
noncomputable def allowed619 : List Nat := [0x40000000000000000000,0x80000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 619. -/
noncomputable def tree619 : ParitySearchTree := (.split 63 (.pack [5]) (.split 64 (.pack [0]) (.split 65 (.pack [4]) (.split 66 (.pack [7]) (.split 67 (.pack [8]) (.split 68 (.pack [9]) (.split 78 .done (.split 79 .done (.split 80 (.pack [4]) (.split 105 (.pack [2]) (.split 106 (.pack [3]) (.split 107 (.pack [1]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 619. -/
theorem checked619 : checkParitySearch 8 (fun q => (rows619 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed619.contains) tree619 0xff8dbb7bf7fffffffffff03ffffff9fdffffdfbffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 620. -/
noncomputable def rows620 : Nat := 0x3000000000000000100000020024000000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008006001400006000400c00d001101900240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 620. -/
noncomputable def allowed620 : List Nat := [0x40000000000000000000,0x80000000000000000000,0x40000000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 620. -/
noncomputable def tree620 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 36 (.pack [5]) (.split 39 (.pack [7]) (.split 40 (.pack [8]) (.split 48 (.pack [9]) (.split 52 (.pack [10]) (.split 64 (.pack [10]) (.split 66 (.pack [12]) (.split 67 (.pack [11]) (.split 78 .done (.split 79 .done (.split 90 .done (.split 105 .done (.split 106 (.pack [1]) (.split 126 (.pack [0]) (.split 128 (.pack [5]) (.split 141 (.pack [3]) (.split 142 (.pack [4]) (.split 155 (.pack [10]) (.zero 6)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 620. -/
theorem checked620 : checkParitySearch 8 (fun q => (rows620 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed620.contains) tree620 0xff8bffbfffffffedfffbf4ffefffdffd7ffdffffcfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 621. -/
noncomputable def rows621 : Nat := 0x300000000000000010000002002400000000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000000000a0000000040000008009002802d000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000036000006c000000000000000000001b018600000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000004008001401402000000400480300340004024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 621. -/
noncomputable def allowed621 : List Nat := [0x40000000000000000000,0x200000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 621. -/
noncomputable def tree621 : ParitySearchTree := (.split 10 (.pack [0]) (.split 13 (.pack [6]) (.split 22 (.pack [2]) (.split 38 (.pack [7]) (.split 40 (.pack [10]) (.split 41 (.pack [8]) (.split 52 (.pack [12]) (.split 53 (.pack [9]) (.split 63 (.pack [11]) (.split 66 (.pack [13]) (.split 78 .done (.split 105 .done (.split 114 (.pack [5]) (.split 116 (.pack [3]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 143 (.pack [5]) (.split 154 (.pack [11]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 621. -/
theorem checked621 : checkParitySearch 8 (fun q => (rows621 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed621.contains) tree621 0xff8bfdfffbffffedfffbf4ffefffdffffffdffdfcfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 622. -/
noncomputable def rows622 : Nat := 0xc000000000000002000000400480000000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000000080000028000000000000000000000400480000000000000000000000003002800000002000600100440098048000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000100120008019005000a004800000008000008a0080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 622. -/
noncomputable def allowed622 : List Nat := [0x100,0x2000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 622. -/
noncomputable def tree622 : ParitySearchTree := (.split 8 .done (.split 55 (.pack [7]) (.split 58 (.pack [10]) (.split 67 (.pack [7]) (.split 68 (.pack [8]) (.split 71 (.pack [9]) (.split 82 (.pack [1]) (.split 86 (.pack [11]) (.split 96 (.pack [1]) (.split 109 .done (.split 110 (.pack [0]) (.split 125 (.pack [3]) (.split 159 (.pack [9]) (.split 161 (.pack [4]) (.split 172 (.pack [5]) (.split 173 (.pack [6]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 622. -/
theorem checked622 : checkParitySearch 8 (fun q => (rows622 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed622.contains) tree622 0xff7fffffff6fffdfe7dfdfff7ff9bffbffff5ffebff8f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 623. -/
noncomputable def rows623 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000300280000000200060010044009804800000000001000000000000000000000010006006000004004000400100940008048000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 623. -/
noncomputable def allowed623 : List Nat := [0x100,0x400000000000000000000,0x1000000000000000000000000,0x2000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 623. -/
noncomputable def tree623 : ParitySearchTree := (.split 8 .done (.split 55 (.pack [6]) (.split 58 (.pack [9]) (.split 67 (.pack [6]) (.split 68 (.pack [7]) (.split 71 (.pack [8]) (.split 82 .done (.split 86 (.pack [10]) (.split 96 .done (.split 109 .done (.split 110 (.pack [0]) (.split 125 (.pack [2]) (.split 159 (.pack [8]) (.split 161 (.pack [3]) (.split 172 (.pack [4]) (.split 173 (.pack [5]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 623. -/
theorem checked623 : checkParitySearch 8 (fun q => (rows623 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed623.contains) tree623 0xff7ffffb7ff7fedfe6ffddff7ff9fffbf3fffffefff3f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 624. -/
noncomputable def rows624 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000300280000000200060010044009804800000000001000000000000000000000010006006000004004000400100940008048000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 624. -/
noncomputable def allowed624 : List Nat := [0x100,0x400000000000000000000,0x1000000000000000000000000,0x2000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 624. -/
noncomputable def tree624 : ParitySearchTree := (.split 8 .done (.split 55 (.pack [6]) (.split 58 (.pack [9]) (.split 67 (.pack [6]) (.split 68 (.pack [7]) (.split 71 (.pack [8]) (.split 82 .done (.split 86 (.pack [10]) (.split 96 .done (.split 109 .done (.split 110 (.pack [0]) (.split 125 (.pack [2]) (.split 159 (.pack [8]) (.split 161 (.pack [3]) (.split 172 (.pack [4]) (.split 173 (.pack [5]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 624. -/
theorem checked624 : checkParitySearch 8 (fun q => (rows624 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed624.contains) tree624 0xff7fffedffdffedfe6ffddff7ff9fffbf9ffffffbff3f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 625. -/
noncomputable def rows625 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000180000000000000008000001001200000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000100300060200000000010006004c02000480001001200000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 625. -/
noncomputable def allowed625 : List Nat := [0x100000,0x20000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 625. -/
noncomputable def tree625 : ParitySearchTree := (.split 5 (.pack [3]) (.split 8 (.pack [2]) (.split 20 .done (.split 39 (.pack [7]) (.split 42 (.pack [8]) (.split 57 (.pack [13]) (.split 66 (.pack [14]) (.split 67 (.pack [11]) (.split 70 (.pack [12]) (.split 81 (.pack [0]) (.split 82 (.pack [1]) (.split 96 (.pack [1]) (.split 137 .done (.split 145 (.pack [5]) (.split 146 (.pack [6]) (.split 160 (.pack [9]) (.split 161 (.pack [12]) (.split 172 (.pack [10]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 625. -/
theorem checked625 : checkParitySearch 8 (fun q => (rows625 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed625.contains) tree625 0xff7fffedfe6fff9ff0fffdfffffdfffbf9ff3fff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 626. -/
noncomputable def rows626 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000006c000000024000009000100480410000000000120100000000000000000000000000004006000200c00140090000000000020014034

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 626. -/
noncomputable def allowed626 : List Nat := [0x4,0x80000000000000000000,0x40000000000000000000000,0x400000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 626. -/
noncomputable def tree626 : ParitySearchTree := (.split 2 .done (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 14 (.pack [4]) (.split 16 (.pack [5]) (.split 29 (.pack [6]) (.split 76 (.pack [11]) (.split 79 .done (.split 90 .done (.split 92 (.pack [10]) (.split 106 .done (.split 107 (.pack [1]) (.split 117 (.pack [5]) (.split 133 (.pack [8]) (.split 134 (.pack [7]) (.split 146 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 626. -/
theorem checked626 : checkParitySearch 8 (fun q => (rows626 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed626.contains) tree626 0xff7ffeffffffffdbffd3fd7feffe67ff7ff7ffffd7ffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 627. -/
noncomputable def rows627 : Nat := 0x600000000000000020000004004800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000001000000c00240000000000000000008000000000000000000000300300000000080080090002001811f0000000000040000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 627. -/
noncomputable def allowed627 : List Nat := [0x8000000000000,0x10000000000000,0x1000000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 627. -/
noncomputable def tree627 : ParitySearchTree := (.split 2 (.pack [3]) (.split 48 (.pack [7]) (.split 49 (.pack [8]) (.split 50 (.pack [9]) (.split 51 .done (.split 52 .done (.split 56 (.pack [10]) (.split 63 (.pack [11]) (.split 64 (.pack [12]) (.split 77 (.pack [13]) (.split 92 (.pack [0]) (.split 95 (.pack [2]) (.split 107 (.pack [4]) (.split 119 (.pack [5]) (.split 156 .done (.split 157 (.pack [6]) (.split 168 .done (.split 169 (.pack [14]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 627. -/
theorem checked627 : checkParitySearch 8 (fun q => (rows627 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed627.contains) tree627 0xff7ffb5ff5ffffdbffbffdbfeffe7ffdfff7ffafd7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 628. -/
noncomputable def rows628 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000100000050024000000000000000000800000000000000000000005003000000002000400c004000500d80000000000100000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 628. -/
noncomputable def allowed628 : List Nat := [0x8000000000000,0x10000000000000,0x1000000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 628. -/
noncomputable def tree628 : ParitySearchTree := (.split 4 (.pack [4]) (.split 51 .done (.split 52 .done (.split 54 (.pack [7]) (.split 55 (.pack [8]) (.split 64 (.pack [9]) (.split 66 (.pack [10]) (.split 82 (.pack [2]) (.split 94 (.pack [0]) (.split 95 (.pack [0]) (.split 106 (.pack [3]) (.split 121 (.pack [5]) (.split 156 .done (.split 157 (.pack [6]) (.split 168 .done (.split 170 (.pack [10]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 628. -/
theorem checked628 : checkParitySearch 8 (fun q => (rows628 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed628.contains) tree628 0xff7ffb5ff5ffffb7ff7ffdbff7fe7ffdfff7ffafe7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 629. -/
noncomputable def rows629 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000010010006006000004004000800100940008048000000000000000000000000000000004000003000000000000000000000020024000000000000000000000001b000000009000002400000120104000000000048041000000000000000000000c0030000000020020005000804400d800000000001000000000000000000000000000000000004000000600900000000000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 629. -/
noncomputable def allowed629 : List Nat := [0x100,0x400000000000000000,0x1000000000000000000000000,0x40000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 629. -/
noncomputable def tree629 : ParitySearchTree := (.split 8 .done (.split 55 (.pack [8]) (.split 56 (.pack [9]) (.split 58 (.pack [10]) (.split 59 (.pack [11]) (.split 70 .done (.split 74 (.pack [11]) (.split 83 (.pack [0]) (.split 96 .done (.split 98 (.pack [4]) (.split 113 (.pack [2]) (.split 125 (.pack [3]) (.split 160 (.pack [5]) (.split 161 (.pack [6]) (.split 174 .done (.split 175 (.pack [7]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 629. -/
theorem checked629 : checkParitySearch 8 (fun q => (rows629 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed629.contains) tree629 0xff7ff7ffffb7ff7fe4ff5ff9fff5ffdfffbf3ffffff7f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 630. -/
noncomputable def rows630 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000010010006006000004004000800100940008048000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000500300360200000000010006004c000020800010012000000000000000000000c0030000000020020005000804400d800000000001000000000000000000000000000000000004000000600900000000000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 630. -/
noncomputable def allowed630 : List Nat := [0x100,0x400000000000000000,0x1000000000000000000000000,0x40000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 630. -/
noncomputable def tree630 : ParitySearchTree := (.split 8 .done (.split 55 (.pack [8]) (.split 56 (.pack [9]) (.split 58 (.pack [10]) (.split 59 (.pack [11]) (.split 70 .done (.split 74 (.pack [11]) (.split 83 (.pack [0]) (.split 96 .done (.split 98 (.pack [4]) (.split 113 (.pack [2]) (.split 125 (.pack [3]) (.split 160 (.pack [5]) (.split 161 (.pack [6]) (.split 174 .done (.split 175 (.pack [7]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 630. -/
theorem checked630 : checkParitySearch 8 (fun q => (rows630 >>> (256*q)) &&& (2^256-1)) 0x6 (allowed630.contains) tree630 0xff7ff7ffff6ffeffe4ff5ff9fff5ffdfffbf5ffffffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 631. -/
noncomputable def rows631 : Nat := (Nat.lor 0x500000000000000040000008009000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000006000c00c00180000000000000000030030006c000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000010000001800000000000000000000080090000000000000000000000b00a802b008000001002000400080040058480100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000008000006001200000000000000000040 (Nat.shiftLeft 0xc00000000000000200000040048000000000000000000000000000000000000030000000000000001000000200240000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 631. -/
noncomputable def allowed631 : List Nat := [0x100000,0x40000000000000,0x400000000000000000000,0x20000000000000000000000000000000000000,0x20000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 631. -/
noncomputable def tree631 : ParitySearchTree := (.split 5 (.pack [1]) (.split 8 (.pack [4]) (.split 20 .done (.split 31 (.pack [6]) (.split 34 (.pack [7]) (.split 39 (.pack [8]) (.split 40 (.pack [9]) (.split 42 (.pack [10]) (.split 54 .done (.split 67 (.pack [15]) (.split 82 .done (.split 97 (.pack [0]) (.split 108 (.pack [2]) (.split 135 (.pack [11]) (.split 144 (.pack [5]) (.split 145 (.pack [12]) (.split 147 (.pack [13]) (.split 149 .done (.split 159 (.pack [10]) (.split 161 .done (.split 163 (.pack [14]) (.split 172 (.pack [16]) (.split 173 (.pack [12]) (.split 175 (.pack [17]) (.zero 3)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 631. -/
theorem checked631 : checkParitySearch 8 (fun q => (rows631 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed631.contains) tree631 0xff7efbefbfdffedffdffedff7fffff97f9ffedffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 632. -/
noncomputable def rows632 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000180000000000000008000001001200000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000001000000500000000000000000000008009000000000000000000001400180000000100100060004022006c000000000008000000000000000000000000000000000080000060012000000000000000000400000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 632. -/
noncomputable def allowed632 : List Nat := [0x200000000000000,0x400000000000000,0x8000000000000000000000000000000000000000,0x40000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 632. -/
noncomputable def tree632 : ParitySearchTree := (.split 7 (.pack [3]) (.split 54 (.pack [7]) (.split 55 (.pack [8]) (.split 57 .done (.split 58 .done (.split 69 (.pack [9]) (.split 73 (.pack [11]) (.split 82 (.pack [0]) (.split 97 (.pack [1]) (.split 98 (.pack [1]) (.split 112 (.pack [4]) (.split 124 (.pack [5]) (.split 159 .done (.split 160 (.pack [6]) (.split 174 .done (.split 176 (.pack [10]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 632. -/
theorem checked632 : checkParitySearch 8 (fun q => (rows632 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed632.contains) tree632 0xff7e9ff9fff7ffffffff6ff9fff3ff7ff3bfebffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 633. -/
noncomputable def rows633 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000180000000000000008000001001200000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000001000000500000000000000000000008009000000000000000000001400180000000100100060004022006c000000000008000000000000000000000000000000000080000060012000000000000000000400000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 633. -/
noncomputable def allowed633 : List Nat := [0x200000000000000,0x400000000000000,0x8000000000000000000000000000000000000000,0x40000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 633. -/
noncomputable def tree633 : ParitySearchTree := (.split 7 (.pack [3]) (.split 54 (.pack [7]) (.split 55 (.pack [8]) (.split 57 .done (.split 58 .done (.split 69 (.pack [9]) (.split 73 (.pack [11]) (.split 82 (.pack [0]) (.split 97 (.pack [1]) (.split 98 (.pack [1]) (.split 112 (.pack [4]) (.split 124 (.pack [5]) (.split 159 .done (.split 160 (.pack [6]) (.split 174 .done (.split 176 (.pack [10]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 633. -/
theorem checked633 : checkParitySearch 8 (fun q => (rows633 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed633.contains) tree633 0xff7e9fef7fdfffffffff6ff9fff3ff7ff9bfebfefffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 634. -/
noncomputable def rows634 : Nat := 0x300000000000000010000002002400000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000100000050000000000000000000000800900000000000000000000033000000026000005400000d00ca00000000001301160000000000000000000033000000009000000400000d00ca000000000004804100000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 634. -/
noncomputable def allowed634 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 634. -/
noncomputable def tree634 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 4 (.pack [1]) (.split 8 (.pack [2]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 20 (.pack [8]) (.split 65 (.pack [0]) (.split 67 (.pack [14]) (.split 70 (.pack [12]) (.split 71 (.pack [13]) (.split 80 (.pack [3]) (.split 82 (.pack [1]) (.split 83 (.pack [2]) (.split 106 (.pack [14]) (.split 108 (.pack [5]) (.split 110 (.pack [5]) (.split 133 (.pack [9]) (.split 134 (.pack [9]) (.split 137 (.pack [10]) (.split 168 (.pack [14]) (.split 169 (.pack [11]) (.split 172 (.pack [15]) (.split 173 (.pack [15]) (.zero 4)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 634. -/
theorem checked634 : checkParitySearch 8 (fun q => (rows634 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed634.contains) tree634 0xff7dfedffffffffffd43fa3ffffef7fffff6fffffffd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 635. -/
noncomputable def rows635 : Nat := 0x30000000000000001000000200240000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000200000030000000000000000000001001200000000000000000000035000000016000003800000c80d100000000000b00a60000000000000000000035000000009000000800000c80d10000000000048041000000000000000000000000000000001000000500240000000000000000008000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000c00000000200000000048030036000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 635. -/
noncomputable def allowed635 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 635. -/
noncomputable def tree635 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 5 (.pack [1]) (.split 7 (.pack [2]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 19 (.pack [8]) (.split 64 (.pack [0]) (.split 68 (.pack [14]) (.split 70 (.pack [12]) (.split 71 (.pack [13]) (.split 79 (.pack [3]) (.split 82 (.pack [2]) (.split 83 (.pack [1]) (.split 107 (.pack [14]) (.split 108 (.pack [5]) (.split 109 (.pack [5]) (.split 133 (.pack [9]) (.split 134 (.pack [9]) (.split 136 (.pack [10]) (.split 168 (.pack [14]) (.split 170 (.pack [11]) (.split 172 (.pack [15]) (.split 173 (.pack [15]) (.zero 4)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 635. -/
theorem checked635 : checkParitySearch 8 (fun q => (rows635 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed635.contains) tree635 0xff7dfedffffffffffb83f63fffff77fffff6fffffffe7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 636. -/
noncomputable def rows636 : Nat := 0x3000000000000000100000020024000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000030000000036000000c00000c00d800000000001b01860000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000010000005002400000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 636. -/
noncomputable def allowed636 : List Nat := [0x2,0x4]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 636. -/
noncomputable def tree636 : ParitySearchTree := (.split 1 .done (.split 2 .done (.split 7 (.pack [0]) (.split 8 (.pack [1]) (.split 16 (.pack [4]) (.split 17 (.pack [5]) (.split 19 (.pack [6]) (.split 20 (.pack [7]) (.split 67 (.pack [13]) (.split 68 (.pack [14]) (.split 70 (.pack [11]) (.split 71 (.pack [12]) (.split 82 (.pack [0]) (.split 83 (.pack [1]) (.split 106 (.pack [13]) (.split 107 (.pack [2]) (.split 133 (.pack [8]) (.split 134 (.pack [8]) (.split 136 (.pack [9]) (.split 137 (.pack [9]) (.split 172 (.pack [10]) (.split 173 (.pack [15]) (.zero 3)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 636. -/
theorem checked636 : checkParitySearch 8 (fun q => (rows636 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed636.contains) tree636 0xff7dfedffffffffff9c3f23ffffff7fffff6fffffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 637. -/
noncomputable def rows637 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000030000000030000000000000c00d800000000001801b00000000000000000000030000000008000000000000c00d8000000000004004800000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000010000005002400000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 637. -/
noncomputable def allowed637 : List Nat := [0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 637. -/
noncomputable def tree637 : ParitySearchTree := (.split 4 .done (.split 5 .done (.split 7 (.pack [0]) (.split 8 (.pack [1]) (.split 19 (.pack [4]) (.split 20 (.pack [5]) (.split 67 (.pack [10]) (.split 68 (.pack [11]) (.split 70 (.pack [8]) (.split 71 (.pack [9]) (.split 82 (.pack [0]) (.split 83 (.pack [1]) (.split 136 (.pack [6]) (.split 137 (.pack [6]) (.split 172 (.pack [7]) (.split 173 (.pack [2]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 637. -/
theorem checked637 : checkParitySearch 8 (fun q => (rows637 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed637.contains) tree637 0xff7dfedffffffffff8c7f07fffffbffffff6ffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 638. -/
noncomputable def rows638 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000030000000030000000000000c00d800000000001801b00000000000000000000030000000008000000000000c00d800000000000400480000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000001000000500240000000000000000008000000000000000000000000060000000010000000002401801b0000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 638. -/
noncomputable def allowed638 : List Nat := [0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 638. -/
noncomputable def tree638 : ParitySearchTree := (.split 4 .done (.split 5 .done (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 67 (.pack [0]) (.split 68 (.pack [11]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 82 (.pack [1]) (.split 83 (.pack [2]) (.split 136 (.pack [7]) (.split 137 (.pack [7]) (.split 172 (.pack [8]) (.split 173 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 638. -/
theorem checked638 : checkParitySearch 8 (fun q => (rows638 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed638.contains) tree638 0xff7dfedffffffffff88ff0ffffffaffffff6ffffffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 639. -/
noncomputable def rows639 : Nat := 0x50000000000000004000000800900000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000030000000030000000000000c00d800000000001801b00000000000000000000030000000008000000000000c00d800000000000400480000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000001000000500240000000000000000008000000000000000000000000060000000010000000002401801b0000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 639. -/
noncomputable def allowed639 : List Nat := [0x10,0x20]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 639. -/
noncomputable def tree639 : ParitySearchTree := (.split 4 .done (.split 5 .done (.split 7 (.pack [1]) (.split 8 (.pack [2]) (.split 19 (.pack [5]) (.split 20 (.pack [6]) (.split 67 (.pack [11]) (.split 68 (.pack [0]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 82 (.pack [1]) (.split 83 (.pack [2]) (.split 136 (.pack [7]) (.split 137 (.pack [7]) (.split 172 (.pack [8]) (.split 173 (.pack [3]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 639. -/
theorem checked639 : checkParitySearch 8 (fun q => (rows639 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed639.contains) tree639 0xff7dfedffffffffff857f17fffff9ffffff6ffffffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 640. -/
noncomputable def rows640 : Nat := 0x8000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000004000a00600180000000100000020004022006c000000000000000000000000001001200c00d8000000000000000000800000820000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000033005000000004006800200400c200900000000000200000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 640. -/
noncomputable def allowed640 : List Nat := [0x20000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 640. -/
noncomputable def tree640 : ParitySearchTree := (.split 22 (.pack [4]) (.split 23 (.pack [5]) (.split 25 (.pack [6]) (.split 26 (.pack [7]) (.split 37 (.pack [11]) (.split 41 (.pack [10]) (.split 50 (.pack [12]) (.split 65 .done (.split 92 (.pack [0]) (.split 127 (.pack [2]) (.split 128 (.pack [3]) (.split 141 (.pack [11]) (.split 142 (.pack [6]) (.split 153 (.pack [8]) (.split 155 (.pack [1]) (.split 170 (.pack [1]) (.zero 9)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 640. -/
theorem checked640 : checkParitySearch 8 (fun q => (rows640 >>> (256*q)) &&& (2^256-1)) 0x202 (allowed640.contains) tree640 0xff79ffbfffbffbfffffffb7febfe67fdfff2ffefffdff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 641. -/
noncomputable def rows641 : Nat := (Nat.lor 0x3000000000000000100000020024000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000024000606c000000024000c048040805304100000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000002002000c00c00000800800100020160008048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000010000005002400000000000000000080 (Nat.shiftLeft 0x28000000000000002000000400480000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 641. -/
noncomputable def allowed641 : List Nat := [0x8000000000000000,0x80000000000000000000,0x40000000000000000000000,0x4000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 641. -/
noncomputable def tree641 : ParitySearchTree := (.split 36 (.pack [6]) (.split 42 (.pack [9]) (.split 48 (.pack [10]) (.split 49 (.pack [11]) (.split 52 (.pack [13]) (.split 54 (.pack [15]) (.split 63 .done (.split 70 (.pack [16]) (.split 79 .done (.split 82 (.pack [0]) (.split 90 .done (.split 91 (.pack [8]) (.split 106 (.pack [1]) (.split 109 (.pack [2]) (.split 142 (.pack [3]) (.split 143 (.pack [13]) (.split 145 (.pack [4]) (.split 146 (.pack [5]) (.split 153 (.pack [6]) (.split 154 (.pack [7]) (.split 170 .done (.split 173 (.pack [14]) (.zero 12)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 641. -/
theorem checked641 : checkParitySearch 8 (fun q => (rows641 >>> (256*q)) &&& (2^256-1)) 0x1000 (allowed641.contains) tree641 0xff77fe7fffffffffffdbf4ffebfe6ffd7ff3ffffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 642. -/
noncomputable def rows642 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000000000036000000048000009008200d80c300000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000002000001800080000000000000000010010000000000000000000000014013005a01004000a001008801700480020900200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 642. -/
noncomputable def allowed642 : List Nat := [0x20,0x8000000000,0x80000000000000000,0x800000000000000000000000000000000,0x4000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 642. -/
noncomputable def tree642 : ParitySearchTree := (.split 5 .done (.split 16 (.pack [3]) (.split 19 (.pack [4]) (.split 25 (.pack [5]) (.split 39 .done (.split 42 (.pack [10]) (.split 52 (.pack [11]) (.split 53 (.pack [12]) (.split 54 (.pack [13]) (.split 56 (.pack [14]) (.split 67 .done (.split 71 (.pack [14]) (.split 80 (.pack [8]) (.split 93 (.pack [13]) (.split 95 (.pack [0]) (.split 110 (.pack [4]) (.split 120 (.pack [6]) (.split 129 (.pack [2]) (.split 131 .done (.split 132 (.pack [7]) (.split 134 .done (.split 144 (.pack [9]) (.split 145 (.pack [9]) (.split 148 (.pack [10]) (.split 158 (.pack [13]) (.split 160 (.pack [14]) (.zero 1)))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 642. -/
theorem checked642 : checkParitySearch 8 (fun q => (rows642 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed642.contains) tree642 0xff6ffeffb7dfffb7fdbffbfffffeffffffeff27ffbff3 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 643. -/
noncomputable def rows643 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000001000400c001808000001001200180130080012000000000000000000000030000000008000000000000c00d80000000000040048000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000002000001800080000000000000000010010000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 643. -/
noncomputable def allowed643 : List Nat := [0x100000000000000000000,0x800000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 643. -/
noncomputable def tree643 : ParitySearchTree := (.split 9 (.pack [0]) (.split 12 (.pack [1]) (.split 27 (.pack [9]) (.split 36 (.pack [10]) (.split 37 (.pack [7]) (.split 40 (.pack [8]) (.split 51 (.pack [11]) (.split 52 (.pack [12]) (.split 65 (.pack [13]) (.split 68 (.pack [3]) (.split 80 .done (.split 107 .done (.split 115 (.pack [6]) (.split 116 (.pack [5]) (.split 130 (.pack [2]) (.split 131 (.pack [8]) (.split 142 (.pack [5]) (.split 156 (.pack [12]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 643. -/
theorem checked643 : checkParitySearch 8 (fun q => (rows643 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed643.contains) tree643 0xff4fffdffdffffb7f9bff77ffbfffffdfff7ffefe7fcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 644. -/
noncomputable def rows644 : Nat := 0x50000000000000004000000800900000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000200000030048000000000000000001000000000000000000000003006000000004000800a008000a01b00000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 644. -/
noncomputable def allowed644 : List Nat := [0x10000000000000,0x20000000000000,0x2000000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 644. -/
noncomputable def tree644 : ParitySearchTree := (.split 5 (.pack [4]) (.split 52 .done (.split 53 .done (.split 55 (.pack [7]) (.split 56 (.pack [8]) (.split 65 (.pack [9]) (.split 67 (.pack [10]) (.split 83 (.pack [2]) (.split 93 (.pack [0]) (.split 95 (.pack [0]) (.split 107 (.pack [3]) (.split 122 (.pack [5]) (.split 157 .done (.split 158 (.pack [6]) (.split 168 (.pack [10]) (.split 169 .done (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 644. -/
theorem checked644 : checkParitySearch 8 (fun q => (rows644 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed644.contains) tree644 0xfefffe9ffd7ff7fffffffb7febfebfff7feaffcfffbff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 645. -/
noncomputable def rows645 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000000000000000000001c000003803f00000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000000008000000c002000000000000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000200000180008000000000000000001001000000000000000000001e005000000001003200800400608090000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 645. -/
noncomputable def allowed645 : List Nat := [0x10000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 645. -/
noncomputable def tree645 : ParitySearchTree := (.split 60 (.pack [4]) (.split 61 (.pack [5]) (.split 62 (.pack [6]) (.split 63 (.pack [0]) (.split 64 .done (.split 65 (.pack [8]) (.split 75 (.pack [9]) (.split 76 (.pack [10]) (.split 77 (.pack [11]) (.split 102 (.pack [2]) (.split 103 (.pack [3]) (.split 104 (.pack [1]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 645. -/
theorem checked645 : checkParitySearch 8 (fun q => (rows645 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed645.contains) tree645 0xfdf1ff9ffeffeffffffff93ff3ff3fffffdbffbfff7ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 646. -/
noncomputable def rows646 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000006006000c00000000000c000001801800360000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000004000003000000000000000000000020024000000000000000000001b0000000120000012000001201040000000000900820000000000000000000000000000000004000003000900000000000000000020000000000000000000005801400580000080100150004004002022c08009000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 646. -/
noncomputable def allowed646 : List Nat := [0x80,0x800000000,0x200000000000000,0x1000000000000000000000000,0x100000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 646. -/
noncomputable def tree646 : ParitySearchTree := (.split 7 .done (.split 20 (.pack [3]) (.split 23 (.pack [6]) (.split 35 .done (.split 42 (.pack [7]) (.split 43 (.pack [8]) (.split 45 (.pack [10]) (.split 49 (.pack [12]) (.split 57 .done (.split 70 (.pack [14]) (.split 82 (.pack [14]) (.split 96 .done (.split 98 (.pack [0]) (.split 100 (.pack [2]) (.split 112 (.pack [4]) (.split 123 (.pack [0]) (.split 147 (.pack [5]) (.split 148 (.pack [9]) (.split 150 (.pack [11]) (.split 162 (.pack [13]) (.split 164 .done (.split 175 (.pack [3]) (.split 176 (.pack [9]) (.split 178 (.pack [15]) (.zero 1)))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 646. -/
theorem checked646 : checkParitySearch 8 (fun q => (rows646 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed646.contains) tree646 0xfbf7dfedff6ffefff6ff7ff9fffdfcbfffffcfffffeff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 647. -/
noncomputable def rows647 : Nat := (Nat.lor 0x140000000000000010000002002400000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000010000001800000000000000000000080090000000000000000000001a809001800d0000110000024020806002404101001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000002000000a00480000000000000000010 (Nat.shiftLeft 0x1800000000000000080000010012000000000000000000000000000000000000030000000000000001000000200240000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 647. -/
noncomputable def allowed647 : List Nat := [0x20,0x40000000000,0x80000000000000000,0x4000000000000000000000000000000000,0x8000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 647. -/
noncomputable def tree647 : ParitySearchTree := (.split 5 .done (.split 8 (.pack [2]) (.split 20 (.pack [8]) (.split 28 (.pack [6]) (.split 34 (.pack [7]) (.split 42 .done (.split 45 (.pack [12]) (.split 57 (.pack [13]) (.split 58 (.pack [15]) (.split 67 .done (.split 73 (.pack [15]) (.split 82 (.pack [0]) (.split 85 (.pack [1]) (.split 108 (.pack [3]) (.split 112 (.pack [5]) (.split 132 (.pack [9]) (.split 134 .done (.split 135 (.pack [10]) (.split 147 (.pack [11]) (.split 148 (.pack [11]) (.split 160 (.pack [13]) (.split 163 (.pack [14]) (.split 171 .done (.split 173 (.pack [16]) (.split 175 (.pack [17]) (.split 176 (.pack [11]) (.zero 4)))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 647. -/
theorem checked647 : checkParitySearch 8 (fun q => (rows647 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed647.contains) tree647 0xfbeff6fdbfdfffbffdbffbfffff2ffffff77f3ffdfff7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 648. -/
noncomputable def rows648 : Nat := 0x50000000000000004000000800900000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000004004004800600600000000000000020004003023e0000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000100000018024000000000000000000800000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000000000400000300090000000000000000002000000000000000000000800000d80000000480000110082009008200000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 648. -/
noncomputable def allowed648 : List Nat := [0x1000,0x2000,0x200000000000000000000000000000,0x200000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 648. -/
noncomputable def tree648 : ParitySearchTree := (.split 9 (.pack [1]) (.split 10 (.pack [2]) (.split 11 (.pack [3]) (.split 12 .done (.split 13 .done (.split 17 (.pack [4]) (.split 24 (.pack [6]) (.split 25 (.pack [7]) (.split 38 (.pack [8]) (.split 53 (.pack [12]) (.split 117 .done (.split 118 (.pack [0]) (.split 129 .done (.split 130 (.pack [9]) (.split 143 (.pack [10]) (.split 146 (.pack [11]) (.split 158 (.pack [13]) (.split 170 (.pack [14]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 648. -/
theorem checked648 : checkParitySearch 8 (fun q => (rows648 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed648.contains) tree648 0xdffdffffedfefff6bfebffbffe7fffffefcffcfffbffe 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 649. -/
noncomputable def rows649 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000c0000000020000000000803003600000000000100100000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a0048000000000000000001000000000000000000000000000060000000000001801b0000000000030036006

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 649. -/
noncomputable def allowed649 : List Nat := [0x2000,0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 649. -/
noncomputable def tree649 : ParitySearchTree := (.split 1 (.pack [4]) (.split 2 (.pack [5]) (.split 13 .done (.split 14 .done (.split 16 (.pack [4]) (.split 17 (.pack [5]) (.split 28 (.pack [6]) (.split 29 (.pack [7]) (.split 76 (.pack [3]) (.split 77 (.pack [3]) (.split 79 (.pack [1]) (.split 80 (.pack [2]) (.split 91 (.pack [9]) (.split 92 (.pack [10]) (.split 145 (.pack [8]) (.split 146 (.pack [8]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 649. -/
theorem checked649 : checkParitySearch 8 (fun q => (rows649 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed649.contains) tree649 0xdffdffff6ffefff03fe3ffbfff7fffffee7ffffff7fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 650. -/
noncomputable def rows650 : Nat := 0x38000007007e0000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000000000000000038000007007e000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000030000000030000006006c00c00d80000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 650. -/
noncomputable def allowed650 : List Nat := [0x2000000000000000000,0x4000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 650. -/
noncomputable def tree650 : ParitySearchTree := (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 60 (.pack [10]) (.split 61 (.pack [8]) (.split 62 (.pack [9]) (.split 72 (.pack [3]) (.split 73 .done (.split 74 .done (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 650. -/
theorem checked650 : checkParitySearch 8 (fun q => (rows650 >>> (256*q)) &&& (2^256-1)) 0x488 (allowed650.contains) tree650 0x3fe3ffb7ff7ffffffdbffbffffff7fffdffffffbfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 651. -/
noncomputable def rows651 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000000000000000038000007007e000000000000000000000000000000000000018000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000028000000010000002002400a00b40000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 651. -/
noncomputable def allowed651 : List Nat := [0x1000000000000000000,0x4000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 651. -/
noncomputable def tree651 : ParitySearchTree := (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 60 (.pack [8]) (.split 61 (.pack [3]) (.split 62 (.pack [9]) (.split 72 .done (.split 73 (.pack [3]) (.split 74 .done (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 651. -/
theorem checked651 : checkParitySearch 8 (fun q => (rows651 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed651.contains) tree651 0x3fe3ff6ffefffffffb7ff7fffffeffffbffffff7fffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 652. -/
noncomputable def rows652 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000000000000000038000007007e0000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000000180000000200000040048006006c0000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 652. -/
noncomputable def allowed652 : List Nat := [0x1000000000000000000,0x2000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 652. -/
noncomputable def tree652 : ParitySearchTree := (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 60 (.pack [8]) (.split 61 (.pack [9]) (.split 62 (.pack [3]) (.split 72 .done (.split 73 .done (.split 74 (.pack [3]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 652. -/
theorem checked652 : checkParitySearch 8 (fun q => (rows652 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed652.contains) tree652 0x3fe3fedffdfffffff6ffeffffffdffff7fffffeffffc 0 1 = true := by decide +kernel

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

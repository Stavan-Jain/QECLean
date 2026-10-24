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
/-- Packed parity neighborhoods for affine fiber 204. -/
noncomputable def rows204 : Nat := 0x28000000000000002000000400480000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000007002200000d80000000800000100118036008200000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000002000000300480000000000000000010000000000000000000000030006000000040008009008000c01dc0000000000200000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 204. -/
noncomputable def allowed204 : List Nat := [0x8000000000000,0x10000000000000,0x200000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 204. -/
noncomputable def tree204 : ParitySearchTree := (.split 5 (.pack [4]) (.split 50 (.pack [8]) (.split 51 .done (.split 52 .done (.split 54 (.pack [9]) (.split 55 (.pack [10]) (.split 56 (.pack [11]) (.split 66 (.pack [12]) (.split 67 (.pack [13]) (.split 83 (.pack [2]) (.split 92 (.pack [6]) (.split 95 (.pack [0]) (.split 107 (.pack [3]) (.split 122 (.pack [5]) (.split 153 .done (.split 154 (.pack [7]) (.split 168 .done (.split 169 (.pack [12]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 204. -/
theorem checked204 : checkParitySearch 8 (fun q => (rows204 >>> (256*q)) &&& (2^256-1)) 0x42 (allowed204.contains) tree204 0xfffdfa7ff5ffffffffb7fd3fe7ffdffdfffeffafffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 205. -/
noncomputable def rows205 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000004000001400000000000000000000020024000000000000000000000000007002200000d800000008000001001180360082000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 205. -/
noncomputable def allowed205 : List Nat := [0x8000000000000,0x10000000000000,0x200000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 205. -/
noncomputable def tree205 : ParitySearchTree := (.split 21 (.pack [2]) (.split 27 (.pack [4]) (.split 37 (.pack [6]) (.split 38 (.pack [8]) (.split 40 (.pack [7]) (.split 41 (.pack [9]) (.split 51 .done (.split 52 .done (.split 56 (.pack [9]) (.split 68 (.pack [11]) (.split 95 (.pack [0]) (.split 127 (.pack [1]) (.split 128 (.pack [6]) (.split 130 (.pack [3]) (.split 131 (.pack [7]) (.split 153 .done (.split 157 (.pack [7]) (.split 168 .done (.split 169 (.pack [10]) (.split 170 (.pack [10]) (.zero 5)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 205. -/
theorem checked205 : checkParitySearch 8 (fun q => (rows205 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed205.contains) tree205 0xfffdfa7ff5ffffffff6ffcbfe7ffeffdfffeffafffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 206. -/
noncomputable def rows206 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000004000001400100000000000000000020020000000000000000000003c0060000000080098000001010e01b000000000004000000000000000000000500060000000040040018001008801b0000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 206. -/
noncomputable def allowed206 : List Nat := [0x8000000000000,0x10000000000000,0x200000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 206. -/
noncomputable def tree206 : ParitySearchTree := (.split 1 (.pack [3]) (.split 48 (.pack [8]) (.split 49 (.pack [7]) (.split 51 .done (.split 52 .done (.split 63 (.pack [9]) (.split 67 (.pack [10]) (.split 76 (.pack [11]) (.split 91 (.pack [0]) (.split 92 (.pack [0]) (.split 106 (.pack [4]) (.split 118 (.pack [5]) (.split 153 .done (.split 154 (.pack [6]) (.split 168 .done (.split 170 (.pack [2]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 206. -/
theorem checked206 : checkParitySearch 8 (fun q => (rows206 >>> (256*q)) &&& (2^256-1)) 0x6 (allowed206.contains) tree206 0xfffdfa7ff5fffffffedfffbfe7ff8ffdfffeffaffffcf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 207. -/
noncomputable def rows207 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140010000000000000000002002000000000000000000000500060000000040040018001008801b0000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 207. -/
noncomputable def allowed207 : List Nat := [0x8000000000000,0x10000000000000,0x200000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 207. -/
noncomputable def tree207 : ParitySearchTree := (.split 1 (.pack [2]) (.split 48 (.pack [7]) (.split 49 (.pack [6]) (.split 51 .done (.split 52 .done (.split 63 (.pack [8]) (.split 67 (.pack [10]) (.split 76 (.pack [11]) (.split 91 (.pack [0]) (.split 92 (.pack [0]) (.split 106 (.pack [3]) (.split 118 (.pack [4]) (.split 153 .done (.split 154 (.pack [5]) (.split 168 .done (.split 170 (.pack [9]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 207. -/
theorem checked207 : checkParitySearch 8 (fun q => (rows207 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed207.contains) tree207 0xfffdf37fe5fffffffffffdbfe7ffcfe5fffeff2ffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 208. -/
noncomputable def rows208 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000400000140010000000000000000002002000000000000000000000500060000000040040018001008801b0000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 208. -/
noncomputable def allowed208 : List Nat := [0x8000000000000,0x10000000000000,0x200000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 208. -/
noncomputable def tree208 : ParitySearchTree := (.split 1 (.pack [2]) (.split 48 (.pack [7]) (.split 49 (.pack [6]) (.split 51 .done (.split 52 .done (.split 63 (.pack [8]) (.split 67 (.pack [10]) (.split 76 (.pack [11]) (.split 91 (.pack [0]) (.split 92 (.pack [0]) (.split 106 (.pack [3]) (.split 118 (.pack [4]) (.split 153 .done (.split 154 (.pack [5]) (.split 168 .done (.split 170 (.pack [9]) (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 208. -/
theorem checked208 : checkParitySearch 8 (fun q => (rows208 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed208.contains) tree208 0xfffdde7fb5fffffffffffdbfe7ffcff1fffefdaffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 209. -/
noncomputable def rows209 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000004004801801b000010012002000002180000104000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000d8000000048000012000000900820000000000240208000000000000000000000000000000008000000c002000000000000000000400400000000000000000000c0180000000100020028020002806c00000000000800

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 209. -/
noncomputable def allowed209 : List Nat := [0x800,0x2000000000000000000,0x8000000000000000000000000,0x40000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 209. -/
noncomputable def tree209 : ParitySearchTree := (.split 11 .done (.split 58 (.pack [10]) (.split 59 (.pack [11]) (.split 61 (.pack [8]) (.split 62 (.pack [9]) (.split 71 (.pack [11]) (.split 73 .done (.split 89 (.pack [1]) (.split 99 .done (.split 101 (.pack [4]) (.split 113 (.pack [2]) (.split 128 (.pack [3]) (.split 163 (.pack [5]) (.split 164 (.pack [6]) (.split 174 .done (.split 175 (.pack [7]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 209. -/
theorem checked209 : checkParitySearch 8 (fun q => (rows209 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed209.contains) tree209 0xfffdbfffffffffff27feefb9fcafffdfedffffffff9ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 210. -/
noncomputable def rows210 : Nat := 0x8000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000001c0000000000000000000000000000e00fc0000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000180000000040000000009006006c0000000000020000000000000000000001401b000008002000000a0018048010400000004005800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 210. -/
noncomputable def allowed210 : List Nat := [0x800]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 210. -/
noncomputable def tree210 : ParitySearchTree := (.split 6 (.pack [0]) (.split 7 (.pack [3]) (.split 8 (.pack [4]) (.split 9 (.pack [2]) (.split 10 (.pack [1]) (.split 11 .done (.split 21 (.pack [6]) (.split 22 (.pack [7]) (.split 23 (.pack [8]) (.split 138 (.pack [9]) (.split 139 (.pack [10]) (.split 140 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 210. -/
theorem checked210 : checkParitySearch 8 (fun q => (rows210 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed210.contains) tree210 0xfffdbffffffffffe07fcefb9fcefffdfedfffffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 211. -/
noncomputable def rows211 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000000010000001800000000000000000000080090000000000000000000000001001000280180060000000000000008001008801b00000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000001000000500240000000000000000008000000000000000000000308001000a0010032006001000240004004000a0032000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000030000020020002002000c00040240000000100020128

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 211. -/
noncomputable def allowed211 : List Nat := [0x80000,0x800000000000,0x8000000000000000000000000000000,0x8000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 211. -/
noncomputable def tree211 : ParitySearchTree := (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 7 (.pack [4]) (.split 8 (.pack [5]) (.split 19 .done (.split 23 (.pack [7]) (.split 32 (.pack [8]) (.split 47 .done (.split 109 (.pack [10]) (.split 110 (.pack [11]) (.split 123 .done (.split 124 (.pack [4]) (.split 135 .done (.split 137 (.pack [0]) (.split 152 (.pack [3]) (.split 164 (.pack [9]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 211. -/
theorem checked211 : checkParitySearch 8 (fun q => (rows211 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed211.contains) tree211 0xfffdbff67fafffeffeffffffdffff9fff9ff1ffebffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 212. -/
noncomputable def rows212 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000001c0000000000000000000000000000e00fc00000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000180000000000006000000000000000c00d801801b00000000000000000000000400000000108028036080000010010007405000900208

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 212. -/
noncomputable def allowed212 : List Nat := [0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 212. -/
noncomputable def tree212 : ParitySearchTree := (.split 42 (.pack [2]) (.split 43 (.pack [3]) (.split 44 (.pack [4]) (.split 45 (.pack [1]) (.split 46 (.pack [0]) (.split 47 .done (.split 57 (.pack [6]) (.split 58 (.pack [7]) (.split 59 (.pack [8]) (.split 174 (.pack [10]) (.split 175 (.pack [10]) (.split 176 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 212. -/
theorem checked212 : checkParitySearch 8 (fun q => (rows212 >>> (256*q)) &&& (2^256-1)) 0x22 (allowed212.contains) tree212 0xfffdbfe47f8fffeffeffffffdffff9ffffff1fffbffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 213. -/
noncomputable def rows213 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000001c0000000000000000000000000000e00fc0000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 213. -/
noncomputable def allowed213 : List Nat := [0x200000000000,0x400000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 213. -/
noncomputable def tree213 : ParitySearchTree := (.split 42 (.pack [0]) (.split 43 (.pack [1]) (.split 44 (.pack [2]) (.split 45 .done (.split 46 .done (.split 47 .done (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 174 (.pack [8]) (.split 175 (.pack [8]) (.split 176 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 213. -/
theorem checked213 : checkParitySearch 8 (fun q => (rows213 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed213.contains) tree213 0xfffdbfac7f47fffffffffffffffff9ffafffdffa3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 214. -/
noncomputable def rows214 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000001c0000000000000000000000000000e00fc0000000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000008000006000000000000000000000040048000000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 214. -/
noncomputable def allowed214 : List Nat := [0x200000000000,0x400000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 214. -/
noncomputable def tree214 : ParitySearchTree := (.split 42 (.pack [0]) (.split 43 (.pack [1]) (.split 44 (.pack [2]) (.split 45 .done (.split 46 .done (.split 47 .done (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 174 (.pack [8]) (.split 175 (.pack [8]) (.split 176 (.pack [7]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 214. -/
theorem checked214 : checkParitySearch 8 (fun q => (rows214 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed214.contains) tree214 0xfffdbf747ec7fffffffffffffffff9ffcfffdff63ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 215. -/
noncomputable def rows215 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000000000000000001c000003803f00000000000000000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 215. -/
noncomputable def allowed215 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 215. -/
noncomputable def tree215 : ParitySearchTree := (.split 48 .done (.split 49 .done (.split 50 .done (.split 51 (.pack [4]) (.split 52 (.pack [5]) (.split 53 (.pack [6]) (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 90 (.pack [1]) (.split 91 (.pack [2]) (.split 92 (.pack [0]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 215. -/
theorem checked215 : checkParitySearch 8 (fun q => (rows215 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed215.contains) tree215 0xfffdbf15fe1ffffffffffffffffff9fff9ffdff0fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 216. -/
noncomputable def rows216 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000000000000000001c000003803f00000000000000000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 216. -/
noncomputable def allowed216 : List Nat := [0x1000000000000,0x2000000000000,0x4000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 216. -/
noncomputable def tree216 : ParitySearchTree := (.split 48 .done (.split 49 .done (.split 50 .done (.split 51 (.pack [4]) (.split 52 (.pack [5]) (.split 53 (.pack [6]) (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 90 (.pack [1]) (.split 91 (.pack [2]) (.split 92 (.pack [0]) (.zero 3)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 216. -/
theorem checked216 : checkParitySearch 8 (fun q => (rows216 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed216.contains) tree216 0xfffdbf0efe2ffffffffffffffffff9fff5ffdff17ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 217. -/
noncomputable def rows217 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c0000000080010014000001403600000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 217. -/
noncomputable def allowed217 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 217. -/
noncomputable def tree217 : ParitySearchTree := (.split 2 (.pack [3]) (.split 14 (.pack [5]) (.split 61 .done (.split 62 .done (.split 64 (.pack [9]) (.split 65 (.pack [8]) (.split 74 (.pack [10]) (.split 76 (.pack [0]) (.split 102 (.pack [1]) (.split 104 (.pack [1]) (.split 116 (.pack [4]) (.split 131 (.pack [6]) (.split 166 .done (.split 167 (.pack [7]) (.split 177 (.pack [11]) (.split 178 .done (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 217. -/
theorem checked217 : checkParitySearch 8 (fun q => (rows217 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed217.contains) tree217 0xfffdaff2fffffffffff6ff57fd7ffe5fdfff97fffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 218. -/
noncomputable def rows218 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000a00400140180000000100000020021004a0120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000a00000000800c00040180020012000000000004002806

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 218. -/
noncomputable def allowed218 : List Nat := [0x10000000000000000000,0x80000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 218. -/
noncomputable def tree218 : ParitySearchTree := (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 11 (.pack [3]) (.split 13 (.pack [4]) (.split 26 (.pack [5]) (.split 73 (.pack [10]) (.split 76 .done (.split 89 (.pack [11]) (.split 103 .done (.split 104 (.pack [8]) (.split 114 (.pack [4]) (.split 130 (.pack [7]) (.split 131 (.pack [6]) (.split 143 (.pack [9]) (.split 177 (.pack [11]) (.split 179 (.pack [8]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 218. -/
theorem checked218 : checkParitySearch 8 (fun q => (rows218 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed218.contains) tree218 0xfffd7ff7fffffffb7ffa7f27ff7ff9ffcfffbffffafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 219. -/
noncomputable def rows219 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000a00400140180000000100000020021004a01200000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00200000000000000000040040000000000000000000a00000000c00400100140000012000000000006004c02

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 219. -/
noncomputable def allowed219 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 219. -/
noncomputable def tree219 : ParitySearchTree := (.split 1 (.pack [2]) (.split 10 (.pack [3]) (.split 11 (.pack [4]) (.split 14 (.pack [1]) (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 73 (.pack [10]) (.split 76 .done (.split 102 (.pack [1]) (.split 104 (.pack [8]) (.split 116 (.pack [11]) (.split 130 (.pack [7]) (.split 142 (.pack [9]) (.split 143 (.pack [9]) (.split 177 (.pack [11]) (.split 179 (.pack [8]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 219. -/
theorem checked219 : checkParitySearch 8 (fun q => (rows219 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed219.contains) tree219 0xfffd7ff7fffffff93ffe7f27fffff9ffcfffbffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 220. -/
noncomputable def rows220 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c0000000080010014000001403600000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 220. -/
noncomputable def allowed220 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 220. -/
noncomputable def tree220 : ParitySearchTree := (.split 2 (.pack [3]) (.split 14 (.pack [5]) (.split 61 .done (.split 62 .done (.split 64 (.pack [9]) (.split 65 (.pack [8]) (.split 74 (.pack [10]) (.split 76 (.pack [0]) (.split 102 (.pack [1]) (.split 104 (.pack [1]) (.split 116 (.pack [4]) (.split 131 (.pack [6]) (.split 166 .done (.split 167 (.pack [7]) (.split 177 (.pack [11]) (.split 178 .done (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 220. -/
theorem checked220 : checkParitySearch 8 (fun q => (rows220 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed220.contains) tree220 0xfffd77f37ffffffffff6ff57fd7ffe3fdfff9bfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 221. -/
noncomputable def rows221 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000e00c00000000000000180000030031007e0000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 221. -/
noncomputable def allowed221 : List Nat := [0x200000000000,0x400000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 221. -/
noncomputable def tree221 : ParitySearchTree := (.split 45 .done (.split 46 .done (.split 47 (.pack [4]) (.split 48 (.pack [6]) (.split 49 (.pack [7]) (.split 50 (.pack [8]) (.split 60 (.pack [9]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 76 (.pack [0]) (.split 77 (.pack [1]) (.split 103 (.pack [2]) (.split 104 (.pack [2]) (.split 166 (.pack [3]) (.split 167 (.pack [9]) (.split 177 (.pack [11]) (.split 178 (.pack [11]) (.split 179 (.pack [10]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 221. -/
theorem checked221 : checkParitySearch 8 (fun q => (rows221 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed221.contains) tree221 0xfffd67e5ffc7fffffffffffffffff99fffffd3fe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 222. -/
noncomputable def rows222 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c0000000080010014000001403600000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 222. -/
noncomputable def allowed222 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 222. -/
noncomputable def tree222 : ParitySearchTree := (.split 2 (.pack [3]) (.split 14 (.pack [5]) (.split 61 .done (.split 62 .done (.split 64 (.pack [9]) (.split 65 (.pack [8]) (.split 74 (.pack [10]) (.split 76 (.pack [0]) (.split 102 (.pack [1]) (.split 104 (.pack [1]) (.split 116 (.pack [4]) (.split 131 (.pack [6]) (.split 166 .done (.split 167 (.pack [7]) (.split 177 (.pack [11]) (.split 178 .done (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 222. -/
theorem checked222 : checkParitySearch 8 (fun q => (rows222 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed222.contains) tree222 0xfffd3ff77ff7fffffff6ff57fd7ffeffd3ff9fffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 223. -/
noncomputable def rows223 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000004000001400000000000000000000020024000000000000000000000b4000000024000012000001201040000000000120104000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c0000000080010014000001403600000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 223. -/
noncomputable def allowed223 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 223. -/
noncomputable def tree223 : ParitySearchTree := (.split 2 (.pack [3]) (.split 14 (.pack [6]) (.split 61 .done (.split 62 .done (.split 64 (.pack [10]) (.split 65 (.pack [9]) (.split 74 (.pack [11]) (.split 76 (.pack [0]) (.split 102 (.pack [1]) (.split 104 (.pack [1]) (.split 116 (.pack [5]) (.split 131 (.pack [7]) (.split 166 .done (.split 167 (.pack [8]) (.split 177 (.pack [4]) (.split 178 .done (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 223. -/
theorem checked223 : checkParitySearch 8 (fun q => (rows223 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed223.contains) tree223 0xfffd3ff3ffffffff6ff7ff57fd5ffeffdfff9fffff5ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 224. -/
noncomputable def rows224 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000c00400100140028000000000000006004c0200048000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 224. -/
noncomputable def allowed224 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 224. -/
noncomputable def tree224 : ParitySearchTree := (.split 19 (.pack [2]) (.split 22 (.pack [3]) (.split 37 (.pack [7]) (.split 46 (.pack [10]) (.split 47 (.pack [8]) (.split 50 (.pack [11]) (.split 61 .done (.split 62 .done (.split 123 (.pack [0]) (.split 125 (.pack [1]) (.split 138 (.pack [9]) (.split 140 (.pack [4]) (.split 152 (.pack [6]) (.split 166 .done (.split 178 .done (.split 179 (.pack [12]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 224. -/
theorem checked224 : checkParitySearch 8 (fun q => (rows224 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed224.contains) tree224 0xfffd3ff3fffffffdbff2ff57fdfffeffdfff9ffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 225. -/
noncomputable def rows225 : Nat := 0x600000000000000100000020024000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000c00400100140028000000000000006004c02000480000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000080000060012000000000000000000400000000000000000000a00000004800000240000150082000000000024020802

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 225. -/
noncomputable def allowed225 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 225. -/
noncomputable def tree225 : ParitySearchTree := (.split 19 (.pack [3]) (.split 22 (.pack [4]) (.split 37 (.pack [8]) (.split 46 (.pack [11]) (.split 47 (.pack [9]) (.split 50 (.pack [12]) (.split 61 .done (.split 62 .done (.split 123 (.pack [1]) (.split 125 (.pack [2]) (.split 138 (.pack [10]) (.split 140 (.pack [5]) (.split 152 (.pack [7]) (.split 166 .done (.split 178 .done (.split 179 (.pack [0]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 225. -/
theorem checked225 : checkParitySearch 8 (fun q => (rows225 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed225.contains) tree225 0xfffd3ff3fffffffb7ffeff57fc7ffeffdfff9ffffafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 226. -/
noncomputable def rows226 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000000600000000000000100000020024000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000c00400100140028000000000000006004c0200048000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 226. -/
noncomputable def allowed226 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 226. -/
noncomputable def tree226 : ParitySearchTree := (.split 19 (.pack [2]) (.split 22 (.pack [3]) (.split 37 (.pack [7]) (.split 46 (.pack [10]) (.split 47 (.pack [8]) (.split 50 (.pack [11]) (.split 61 .done (.split 62 .done (.split 123 (.pack [0]) (.split 125 (.pack [1]) (.split 138 (.pack [9]) (.split 140 (.pack [4]) (.split 152 (.pack [6]) (.split 166 .done (.split 178 .done (.split 179 (.pack [12]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 226. -/
theorem checked226 : checkParitySearch 8 (fun q => (rows226 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed226.contains) tree226 0xfffd3ff3fffffff6ffe6ff57ff7ffeffdfff9ffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 227. -/
noncomputable def rows227 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000080020004014002800010000002002000680200048000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c0000000080010014000001403600000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 227. -/
noncomputable def allowed227 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 227. -/
noncomputable def tree227 : ParitySearchTree := (.split 2 (.pack [3]) (.split 14 (.pack [6]) (.split 61 .done (.split 62 .done (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 74 (.pack [10]) (.split 76 (.pack [0]) (.split 102 (.pack [1]) (.split 104 (.pack [1]) (.split 116 (.pack [5]) (.split 131 (.pack [7]) (.split 166 .done (.split 167 (.pack [4]) (.split 177 (.pack [11]) (.split 178 .done (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 227. -/
theorem checked227 : checkParitySearch 8 (fun q => (rows227 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed227.contains) tree227 0xfffd3fbbff7ffffffff6ff57fd7ffeff8fff9ffbfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 228. -/
noncomputable def rows228 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c00000000800100140000014036000000000004004000000000000000000000000000000040000014001000000000000000000200200000000000000000000008000000180008001201001040188386078c00000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 228. -/
noncomputable def allowed228 : List Nat := [0x400000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 228. -/
noncomputable def tree228 : ParitySearchTree := (.split 2 (.pack [4]) (.split 14 (.pack [6]) (.split 61 (.pack [8]) (.split 62 (.pack [9]) (.split 64 (.pack [10]) (.split 65 (.pack [11]) (.split 74 (.pack [12]) (.split 76 (.pack [0]) (.split 102 (.pack [2]) (.split 104 (.pack [2]) (.split 116 (.pack [5]) (.split 131 (.pack [7]) (.split 166 .done (.split 167 (.pack [1]) (.split 177 (.pack [13]) (.split 178 (.pack [8]) (.zero 3)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 228. -/
theorem checked228 : checkParitySearch 8 (fun q => (rows228 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed228.contains) tree228 0xfffd3f9fff3ffffffff6ff57fd7ffeffefff9ff9fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 229. -/
noncomputable def rows229 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000600c0000000080010014000001403600000000000400400000000000000000000000000000004000001400100000000000000000020020000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 229. -/
noncomputable def allowed229 : List Nat := [0x2000000000000000,0x4000000000000000,0x400000000000000000000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 229. -/
noncomputable def tree229 : ParitySearchTree := (.split 2 (.pack [3]) (.split 14 (.pack [5]) (.split 61 .done (.split 62 .done (.split 64 (.pack [9]) (.split 65 (.pack [8]) (.split 74 (.pack [10]) (.split 76 (.pack [0]) (.split 102 (.pack [1]) (.split 104 (.pack [1]) (.split 116 (.pack [4]) (.split 131 (.pack [6]) (.split 166 .done (.split 167 (.pack [7]) (.split 177 (.pack [11]) (.split 178 .done (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 229. -/
theorem checked229 : checkParitySearch 8 (fun q => (rows229 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed229.contains) tree229 0xfffd3f63fefffffffff6ff57fd7ffeffefff9ff7fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 230. -/
noncomputable def rows230 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000e00c00000000000000180000030031007e000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 230. -/
noncomputable def allowed230 : List Nat := [0x200000000000,0x400000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 230. -/
noncomputable def tree230 : ParitySearchTree := (.split 45 .done (.split 46 .done (.split 47 .done (.split 48 (.pack [5]) (.split 49 (.pack [6]) (.split 50 (.pack [7]) (.split 60 (.pack [8]) (.split 64 (.pack [6]) (.split 65 (.pack [7]) (.split 76 (.pack [0]) (.split 77 (.pack [1]) (.split 103 (.pack [2]) (.split 104 (.pack [2]) (.split 166 (.pack [3]) (.split 167 (.pack [8]) (.split 177 (.pack [10]) (.split 178 (.pack [10]) (.split 179 (.pack [9]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 230. -/
theorem checked230 : checkParitySearch 8 (fun q => (rows230 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed230.contains) tree230 0xfffd2fe57fc7fffffffffffffffff95fffffd7fe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 231. -/
noncomputable def rows231 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000006008000c018000000008000001001100260120000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000008000002800000000000000000000040048000000000000000000006000000000008009000c00c0104000000000000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 231. -/
noncomputable def allowed231 : List Nat := [0x1000000000000000,0x800000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 231. -/
noncomputable def tree231 : ParitySearchTree := (.split 33 (.pack [2]) (.split 36 (.pack [4]) (.split 45 (.pack [5]) (.split 46 (.pack [6]) (.split 49 (.pack [9]) (.split 60 .done (.split 64 (.pack [9]) (.split 76 (.pack [10]) (.split 103 (.pack [0]) (.split 139 (.pack [1]) (.split 140 (.pack [8]) (.split 150 (.pack [2]) (.split 151 (.pack [3]) (.split 167 .done (.split 177 (.pack [10]) (.split 178 (.pack [0]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 231. -/
theorem checked231 : checkParitySearch 8 (fun q => (rows231 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed231.contains) tree231 0xfffcffefffffffffffcd7ed7fd7ff1ffafff7fffffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 232. -/
noncomputable def rows232 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000006008000c01800000000800000100110026012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000400040040018018000010000002000402c0010090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000008000002800000000000000000000040048000000000000000000008008400c00d8080000000012005001a00004100000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 232. -/
noncomputable def allowed232 : List Nat := [0x1000000000000000,0x800000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 232. -/
noncomputable def tree232 : ParitySearchTree := (.split 33 (.pack [2]) (.split 36 (.pack [5]) (.split 45 (.pack [6]) (.split 46 (.pack [7]) (.split 49 (.pack [10]) (.split 60 .done (.split 64 (.pack [10]) (.split 76 (.pack [11]) (.split 103 (.pack [0]) (.split 139 (.pack [1]) (.split 140 (.pack [9]) (.split 150 (.pack [2]) (.split 151 (.pack [3]) (.split 167 .done (.split 177 (.pack [11]) (.split 178 (.pack [4]) (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 232. -/
theorem checked232 : checkParitySearch 8 (fun q => (rows232 >>> (256*q)) &&& (2^256-1)) 0x101 (allowed232.contains) tree232 0xfffcffefffffffffff797f97fd7fd9ffafff7fffffffc 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 233. -/
noncomputable def rows233 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000006008000c01800000000800000100110026012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000c004000800c0018000180000030030002c040009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000800000280000000000000000000004004800000000000000000000600000000400c00040180010024000000000002004406

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 233. -/
noncomputable def allowed233 : List Nat := [0x1000000000000000,0x800000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 233. -/
noncomputable def tree233 : ParitySearchTree := (.split 33 (.pack [2]) (.split 36 (.pack [5]) (.split 45 (.pack [6]) (.split 46 (.pack [7]) (.split 49 (.pack [10]) (.split 60 .done (.split 64 (.pack [10]) (.split 76 (.pack [11]) (.split 103 (.pack [0]) (.split 139 (.pack [1]) (.split 140 (.pack [9]) (.split 150 (.pack [2]) (.split 151 (.pack [3]) (.split 167 .done (.split 177 (.pack [11]) (.split 178 (.pack [4]) (.zero 8)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 233. -/
theorem checked233 : checkParitySearch 8 (fun q => (rows233 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed233.contains) tree233 0xfffcffeffffffff6fff97e97ff7ff9ffafff7ffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 234. -/
noncomputable def rows234 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000200000180000000000000000000001001200000000000000000000000040000004014001800008000001001000740520090000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000010000001800000000000000000000080090000000000000000000006008000401000280280800000100110026016000804800000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 234. -/
noncomputable def allowed234 : List Nat := [0x1000000000000000,0x800000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 234. -/
noncomputable def tree234 : ParitySearchTree := (.split 7 (.pack [1]) (.split 10 (.pack [6]) (.split 19 (.pack [2]) (.split 33 (.pack [7]) (.split 34 (.pack [11]) (.split 36 (.pack [9]) (.split 45 (.pack [10]) (.split 46 (.pack [11]) (.split 49 (.pack [12]) (.split 60 .done (.split 64 (.pack [13]) (.split 76 (.pack [14]) (.split 103 (.pack [8]) (.split 111 (.pack [5]) (.split 113 (.pack [3]) (.split 123 (.pack [0]) (.split 125 (.pack [7]) (.split 140 (.pack [12]) (.split 150 (.pack [7]) (.split 167 .done (.split 177 (.pack [14]) (.split 178 (.pack [8]) (.zero 4)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 234. -/
theorem checked234 : checkParitySearch 8 (fun q => (rows234 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed234.contains) tree234 0xfffcffa7ff7fffffffe97e97fd7ff9ffffff7ffbfffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 235. -/
noncomputable def rows235 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000400c001400c00000000800000100100014036000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000004002000400c00180000800000100100064040009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000008008400c00d8080000000012005001a00004100000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 235. -/
noncomputable def allowed235 : List Nat := [0x800000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 235. -/
noncomputable def tree235 : ParitySearchTree := (.split 33 (.pack [4]) (.split 34 (.pack [5]) (.split 36 (.pack [6]) (.split 37 (.pack [7]) (.split 46 (.pack [8]) (.split 48 (.pack [10]) (.split 64 (.pack [11]) (.split 76 (.pack [12]) (.split 103 (.pack [0]) (.split 138 (.pack [1]) (.split 139 (.pack [2]) (.split 150 (.pack [4]) (.split 152 (.pack [10]) (.split 166 (.pack [3]) (.split 167 .done (.split 178 (.pack [0]) (.zero 9)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 235. -/
theorem checked235 : checkParitySearch 8 (fun q => (rows235 >>> (256*q)) &&& (2^256-1)) 0x201 (allowed235.contains) tree235 0xfffcff7ffeffffffffe97e97fd7ff9ff9fff7ff7fffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 236. -/
noncomputable def rows236 : Nat := 0x1800000000000000080000010012000000000000000000000000000000000000008000006000000000000000000000040048000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000100000050000000000000000000000800900000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000001000000500000000000000000000008009000000000000000000000000c00400100300060000000000000006004c0200048000000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a00480000000000000000010

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 236. -/
noncomputable def allowed236 : List Nat := [0x200000000000000,0x400000000000000,0x40000000000000000000000000000000000000000,0x40000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 236. -/
noncomputable def tree236 : ParitySearchTree := (.split 15 (.pack [2]) (.split 18 (.pack [3]) (.split 33 (.pack [7]) (.split 42 (.pack [10]) (.split 43 (.pack [8]) (.split 46 (.pack [9]) (.split 57 .done (.split 58 .done (.split 121 (.pack [0]) (.split 122 (.pack [1]) (.split 136 (.pack [4]) (.split 137 (.pack [9]) (.split 148 (.pack [6]) (.split 162 .done (.split 174 .done (.split 175 (.pack [11]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 236. -/
theorem checked236 : checkParitySearch 8 (fun q => (rows236 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed236.contains) tree236 0xfffcd7fd7fffffffffff6fb9fc9fff7fedffebfffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 237. -/
noncomputable def rows237 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000e00c00000000000000180000030031007e0000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 237. -/
noncomputable def allowed237 : List Nat := [0x200000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 237. -/
noncomputable def tree237 : ParitySearchTree := (.split 45 .done (.split 46 (.pack [4]) (.split 47 .done (.split 48 (.pack [6]) (.split 49 (.pack [7]) (.split 50 (.pack [8]) (.split 60 (.pack [9]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 76 (.pack [0]) (.split 77 (.pack [1]) (.split 103 (.pack [2]) (.split 104 (.pack [2]) (.split 166 (.pack [3]) (.split 167 (.pack [9]) (.split 177 (.pack [11]) (.split 178 (.pack [11]) (.split 179 (.pack [10]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 237. -/
theorem checked237 : checkParitySearch 8 (fun q => (rows237 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed237.contains) tree237 0xfffcd7e6ffc7fffffffffffffffff95fffffcbfe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 238. -/
noncomputable def rows238 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000e00c00000000000000180000030031007e000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 238. -/
noncomputable def allowed238 : List Nat := [0x200000000000,0x400000000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 238. -/
noncomputable def tree238 : ParitySearchTree := (.split 45 .done (.split 46 .done (.split 47 .done (.split 48 (.pack [5]) (.split 49 (.pack [6]) (.split 50 (.pack [7]) (.split 60 (.pack [8]) (.split 64 (.pack [6]) (.split 65 (.pack [7]) (.split 76 (.pack [0]) (.split 77 (.pack [1]) (.split 103 (.pack [2]) (.split 104 (.pack [2]) (.split 166 (.pack [3]) (.split 167 (.pack [8]) (.split 177 (.pack [10]) (.split 178 (.pack [10]) (.split 179 (.pack [9]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 238. -/
theorem checked238 : checkParitySearch 8 (fun q => (rows238 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed238.contains) tree238 0xfffc9fe67fc7fffffffffffffffff99fffffcffe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 239. -/
noncomputable def rows239 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000007000000e00fc00000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 239. -/
noncomputable def allowed239 : List Nat := [0x200000000000000,0x400000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 239. -/
noncomputable def tree239 : ParitySearchTree := (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 57 .done (.split 58 .done (.split 59 (.pack [3]) (.split 69 (.pack [8]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 239. -/
theorem checked239 : checkParitySearch 8 (fun q => (rows239 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed239.contains) tree239 0xfffc47f5ffe7fffffffffffffffff9fff9ffc3ff3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 240. -/
noncomputable def rows240 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 240. -/
noncomputable def allowed240 : List Nat := [0x200000000000000,0x400000000000000,0x800000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 240. -/
noncomputable def tree240 : ParitySearchTree := (.split 54 (.pack [3]) (.split 55 (.pack [4]) (.split 56 (.pack [5]) (.split 57 .done (.split 58 .done (.split 59 .done (.split 69 (.pack [7]) (.split 70 (.pack [8]) (.split 71 (.pack [9]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 240. -/
theorem checked240 : checkParitySearch 8 (fun q => (rows240 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed240.contains) tree240 0xfffc47f17feffffffffffffffffff9fff5ffc3ff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 241. -/
noncomputable def rows241 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000007000000e00fc00000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 241. -/
noncomputable def allowed241 : List Nat := [0x200000000000000,0x800000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 241. -/
noncomputable def tree241 : ParitySearchTree := (.split 54 (.pack [4]) (.split 55 (.pack [5]) (.split 56 (.pack [6]) (.split 57 .done (.split 58 (.pack [3]) (.split 59 .done (.split 69 (.pack [8]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 241. -/
theorem checked241 : checkParitySearch 8 (fun q => (rows241 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed241.contains) tree241 0xfffc47eeffd7fffffffffffffffff9fff5ffc3febffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 242. -/
noncomputable def rows242 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 242. -/
noncomputable def allowed242 : List Nat := [0x200000000000000,0x400000000000000,0x800000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 242. -/
noncomputable def tree242 : ParitySearchTree := (.split 54 (.pack [3]) (.split 55 (.pack [4]) (.split 56 (.pack [5]) (.split 57 .done (.split 58 .done (.split 59 .done (.split 69 (.pack [7]) (.split 70 (.pack [8]) (.split 71 (.pack [9]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 242. -/
theorem checked242 : checkParitySearch 8 (fun q => (rows242 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed242.contains) tree242 0xfffc47ea7fdffffffffffffffffff9fff9ffc3fefffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 243. -/
noncomputable def rows243 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000400000300000000000000000000002002400000000000000000000000a0000000040000000001002802d00000000000200200000000000000000000000000000000800000280120000000000000000004000000000000000000000600b400008000400000a0011009010400000004004a00

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 243. -/
noncomputable def allowed243 : List Nat := [0x1000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 243. -/
noncomputable def tree243 : ParitySearchTree := (.split 9 (.pack [3]) (.split 10 (.pack [1]) (.split 11 (.pack [4]) (.split 12 .done (.split 13 (.pack [2]) (.split 14 (.pack [0]) (.split 24 (.pack [6]) (.split 25 (.pack [7]) (.split 26 (.pack [8]) (.split 141 (.pack [10]) (.split 142 (.pack [11]) (.split 143 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 243. -/
theorem checked243 : checkParitySearch 8 (fun q => (rows243 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed243.contains) tree243 0xfffbffffffffffe23fcaff57fafffdffdfffffffcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 244. -/
noncomputable def rows244 : Nat := 0x600000000000000020000004004800000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000c02200a003408000800000a801100b0000104040008040000000000000000000002800a00b40200000000088030026000010400001001000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000400000300090000000000000000002000000000000000000000000000a0000000040000000009002802d0000000000020000000000000000000000800200140140200040080040029026000402400001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 244. -/
noncomputable def allowed244 : List Nat := [0x1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 244. -/
noncomputable def tree244 : ParitySearchTree := (.split 0 .done (.split 22 (.pack [6]) (.split 25 (.pack [10]) (.split 34 (.pack [8]) (.split 49 (.pack [12]) (.split 50 (.pack [11]) (.split 53 (.pack [13]) (.split 60 (.pack [14]) (.split 63 (.pack [15]) (.split 65 (.pack [1]) (.split 78 (.pack [15]) (.split 91 (.pack [5]) (.split 102 (.pack [4]) (.split 117 (.pack [4]) (.split 126 (.pack [2]) (.split 128 (.pack [3]) (.split 138 (.pack [11]) (.split 140 (.pack [7]) (.split 153 (.pack [9]) (.split 167 (.pack [11]) (.zero 0)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 244. -/
theorem checked244 : checkParitySearch 8 (fun q => (rows244 >>> (256*q)) &&& (2^256-1)) 0x11 (allowed244.contains) tree244 0xfffbffbfffffffefbf27fabfef7feffefffdffffc9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 245. -/
noncomputable def rows245 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000400000300000000000000000000002002400000000000000000000002800a00b402000000000880300260000104000010010000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 245. -/
noncomputable def allowed245 : List Nat := [0x1,0x20000000000000000,0x80000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 245. -/
noncomputable def tree245 : ParitySearchTree := (.split 0 .done (.split 12 (.pack [4]) (.split 34 (.pack [6]) (.split 40 (.pack [9]) (.split 61 (.pack [11]) (.split 62 (.pack [12]) (.split 65 .done (.split 76 (.pack [13]) (.split 77 (.pack [14]) (.split 87 (.pack [0]) (.split 91 .done (.split 129 (.pack [9]) (.split 138 (.pack [2]) (.split 140 (.pack [3]) (.split 141 (.pack [4]) (.split 143 (.pack [5]) (.split 153 (.pack [7]) (.split 155 (.pack [8]) (.split 167 (.pack [10]) (.split 169 .done (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 245. -/
theorem checked245 : checkParitySearch 8 (fun q => (rows245 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed245.contains) tree245 0xfffbffbfffffffedff07faffefffe7fefffdffffcfff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 246. -/
noncomputable def rows246 : Nat := 0x4000003000000000000000000000020024000000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000003002f0060050000000000000000001800c8157000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000080000060012000000000000000000400000000000000000000000000000000002000000a00480000000000000000010000000000000000000000000002002c002005600c002400000000001000401440000000000000000000000000a0000000040000000009002802d000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 246. -/
noncomputable def allowed246 : List Nat := [0x1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 246. -/
noncomputable def tree246 : ParitySearchTree := (.split 0 .done (.split 1 (.pack [0]) (.split 2 (.pack [1]) (.split 4 (.pack [2]) (.split 6 (.pack [3]) (.split 8 (.pack [4]) (.split 15 (.pack [7]) (.split 18 (.pack [8]) (.split 19 (.pack [6]) (.split 31 (.pack [9]) (.split 32 (.pack [10]) (.split 108 (.pack [6]) (.split 110 (.pack [6]) (.split 121 (.pack [8]) (.split 122 (.pack [8]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [9]) (.split 135 (.pack [11]) (.split 137 (.pack [11]) (.split 148 (.pack [12]) (.split 149 (.pack [12]) (.zero 5)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 246. -/
theorem checked246 : checkParitySearch 8 (fun q => (rows246 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed246.contains) tree246 0xfffbffbfffffffedfd63febfefff6ffefffdffffcffd7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 247. -/
noncomputable def rows247 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c000000000000000000000080090000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00200000000000000000040040000000000000000000003000c000000008008001400201100360000000000040000000000000000000000000000000000400000140090000000000000000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 247. -/
noncomputable def allowed247 : List Nat := [0x10000000000000,0x20000000000000,0x400000000000000000000000000000000000000,0x2000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 247. -/
noncomputable def tree247 : ParitySearchTree := (.split 2 (.pack [2]) (.split 49 (.pack [7]) (.split 50 (.pack [6]) (.split 52 .done (.split 53 .done (.split 64 (.pack [8]) (.split 68 (.pack [10]) (.split 77 (.pack [11]) (.split 90 (.pack [0]) (.split 92 (.pack [0]) (.split 107 (.pack [3]) (.split 119 (.pack [4]) (.split 154 .done (.split 155 (.pack [5]) (.split 168 (.pack [9]) (.split 169 .done (.zero 1)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 247. -/
theorem checked247 : checkParitySearch 8 (fun q => (rows247 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed247.contains) tree247 0xfffbfcdff9ffffedffdffb7fefffd7ff7ffdffcfcffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 248. -/
noncomputable def rows248 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000002401801b000000000000800000100000104000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000c0028018016800000010000002002200480208000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000008009006006c00000000000000000040000041000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 248. -/
noncomputable def allowed248 : List Nat := [0x80000000,0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 248. -/
noncomputable def tree248 : ParitySearchTree := (.split 31 .done (.split 37 (.pack [6]) (.split 47 .done (.split 50 (.pack [11]) (.split 61 (.pack [12]) (.split 65 (.pack [11]) (.split 77 (.pack [0]) (.split 104 (.pack [1]) (.split 135 (.pack [2]) (.split 137 (.pack [3]) (.split 138 (.pack [9]) (.split 140 (.pack [4]) (.split 151 (.pack [10]) (.split 152 (.pack [5]) (.split 163 (.pack [10]) (.split 165 (.pack [8]) (.split 178 (.pack [14]) (.split 179 (.pack [13]) (.zero 7)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 248. -/
theorem checked248 : checkParitySearch 8 (fun q => (rows248 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed248.contains) tree248 0xfffbeffbefefffeffffffffffffffa5ff87fafff37ff7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 249. -/
noncomputable def rows249 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000002401801b000000000000800000100000104000000000000000000000000000000000200000030000000000000000000001001200000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000010000001800000000000000000000080090000000000000000000000001001000280180060000000000000008001008801b00000000000000000000000000000000020000003004800000000000000000100000000000000000000000000000000001000000500240000000000000000008000000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000030000020020002002000c00040240000000100020128

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 249. -/
noncomputable def allowed249 : List Nat := [0x800000000000,0x8000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 249. -/
noncomputable def tree249 : ParitySearchTree := (.split 4 (.pack [1]) (.split 5 (.pack [2]) (.split 7 (.pack [3]) (.split 8 (.pack [4]) (.split 19 (.pack [7]) (.split 23 (.pack [6]) (.split 32 (.pack [8]) (.split 47 .done (.split 109 (.pack [11]) (.split 110 (.pack [12]) (.split 123 (.pack [7]) (.split 124 (.pack [3]) (.split 135 .done (.split 137 (.pack [0]) (.split 152 (.pack [9]) (.split 164 (.pack [10]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 249. -/
theorem checked249 : checkParitySearch 8 (fun q => (rows249 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed249.contains) tree249 0xfffbeffb7fafffeffeffffffdffffa5ff9ff77febffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 250. -/
noncomputable def rows250 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c000000000000000400000080090000000000000000000000000000000e00a0000000000000014000002802a007e00000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000400000000000060000000000000002002401801b00000000000000000000800200080108030036100000020020006802600000208000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000000008000000c01200000000000000000040000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 250. -/
noncomputable def allowed250 : List Nat := [0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 250. -/
noncomputable def tree250 : ParitySearchTree := (.split 45 (.pack [4]) (.split 46 (.pack [3]) (.split 47 .done (.split 48 (.pack [7]) (.split 49 (.pack [8]) (.split 50 (.pack [9]) (.split 61 (.pack [10]) (.split 63 (.pack [7]) (.split 65 (.pack [9]) (.split 75 (.pack [0]) (.split 77 (.pack [1]) (.split 102 (.pack [2]) (.split 104 (.pack [2]) (.split 165 (.pack [5]) (.split 167 (.pack [11]) (.split 177 (.pack [13]) (.split 178 (.pack [13]) (.split 179 (.pack [12]) (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 250. -/
theorem checked250 : checkParitySearch 8 (fun q => (rows250 >>> (256*q)) &&& (2^256-1)) 0x48 (allowed250.contains) tree250 0xfffbefe97f8fffeffeffffffdffffa5fffff77ffbffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 251. -/
noncomputable def rows251 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000000003000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000080020028005000000006000000c0098040009000000000000000000000000000001200000360000000120000024020802402080000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000000080000060012000000000000000000400000000000000000000000100020010002006000c00240000000800800160040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 251. -/
noncomputable def allowed251 : List Nat := [0x80000000,0x800000000000000,0x1000000000000000000000000000000000,0x8000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 251. -/
noncomputable def tree251 : ParitySearchTree := (.split 28 (.pack [3]) (.split 31 .done (.split 46 (.pack [6]) (.split 55 (.pack [7]) (.split 56 (.pack [8]) (.split 59 .done (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 97 (.pack [1]) (.split 98 (.pack [1]) (.split 132 .done (.split 134 (.pack [2]) (.split 147 .done (.split 149 (.pack [0]) (.split 161 (.pack [4]) (.split 175 (.pack [11]) (.zero 5)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 251. -/
theorem checked251 : checkParitySearch 8 (fun q => (rows251 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed251.contains) tree251 0xfffba7f6eff7ffeffffffffffffffa9ffe7fabfff7ff7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 252. -/
noncomputable def rows252 : Nat := 0x280000000000000020000004004800000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000800100120018003000000000000004004000600ee00000000000000000000000000000000100000018024000000000000000000800000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000000000400000300090000000000000000002000000000000000000000000000000000004000000600900000000000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 252. -/
noncomputable def allowed252 : List Nat := [0x40,0x80,0x1000000000000000000000000000,0x8000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 252. -/
noncomputable def tree252 : ParitySearchTree := (.split 5 (.pack [0]) (.split 6 .done (.split 7 .done (.split 9 (.pack [1]) (.split 10 (.pack [2]) (.split 11 (.pack [3]) (.split 21 (.pack [5]) (.split 22 (.pack [6]) (.split 38 (.pack [7]) (.split 50 (.pack [11]) (.split 108 .done (.split 109 (.pack [13]) (.split 123 .done (.split 124 (.pack [5]) (.split 137 (.pack [8]) (.split 140 (.pack [9]) (.split 152 (.pack [10]) (.split 167 (.pack [12]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 252. -/
theorem checked252 : checkParitySearch 8 (fun q => (rows252 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed252.contains) tree252 0xfffb7ff7ffb7ffefd3ffafffdff5faffffff7ffe7feff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 253. -/
noncomputable def rows253 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000001c0000000000000000000000000000e00fc000000000000000000000000000008009000c00c00000000200000040008006047c00000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000180000000000006000000000000000c00d801801b0000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 253. -/
noncomputable def allowed253 : List Nat := [0x800000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 253. -/
noncomputable def tree253 : ParitySearchTree := (.split 42 (.pack [1]) (.split 43 (.pack [2]) (.split 44 (.pack [3]) (.split 45 (.pack [0]) (.split 46 (.pack [4]) (.split 47 .done (.split 57 (.pack [6]) (.split 58 (.pack [7]) (.split 59 (.pack [8]) (.split 174 (.pack [10]) (.split 175 (.pack [10]) (.split 176 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 253. -/
theorem checked253 : checkParitySearch 8 (fun q => (rows253 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed253.contains) tree253 0xfffb7fcc7fcfffeffeffffffdffffaff9fff7ffdbffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 254. -/
noncomputable def rows254 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000c00200180140000000100000020022004c0240000000000000000000000000004000009000001b00000000800000120104012010400000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 254. -/
noncomputable def allowed254 : List Nat := [0x400000000,0x4000000000000,0x40000000000000000000000000000000000,0x80000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 254. -/
noncomputable def tree254 : ParitySearchTree := (.split 34 .done (.split 37 (.pack [5]) (.split 46 (.pack [6]) (.split 47 (.pack [7]) (.split 50 .done (.split 61 (.pack [8]) (.split 65 (.pack [10]) (.split 77 (.pack [0]) (.split 104 (.pack [1]) (.split 138 .done (.split 140 (.pack [2]) (.split 151 .done (.split 152 (.pack [3]) (.split 165 (.pack [9]) (.split 178 (.pack [12]) (.split 179 (.pack [11]) (.zero 4)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 254. -/
theorem checked254 : checkParitySearch 8 (fun q => (rows254 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed254.contains) tree254 0xfffb7f9bff77ffeffeffffffdffffaffcfff7ff87ffbf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 255. -/
noncomputable def rows255 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000007000000e00fc000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000400000000000060000000000000002002401801b0000000000000000000000002000000a005006c00002000000400580060120041000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 255. -/
noncomputable def allowed255 : List Nat := [0x800000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 255. -/
noncomputable def tree255 : ParitySearchTree := (.split 54 (.pack [5]) (.split 55 (.pack [6]) (.split 56 (.pack [7]) (.split 57 (.pack [4]) (.split 58 (.pack [3]) (.split 59 .done (.split 69 (.pack [9]) (.split 70 (.pack [10]) (.split 71 (.pack [11]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 8)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 255. -/
theorem checked255 : checkParitySearch 8 (fun q => (rows255 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed255.contains) tree255 0xfffa87f4eff7ffeffffffffffffffafffe7fbbfff7ff7 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 256. -/
noncomputable def rows256 : Nat := 0x200000030000000000000000000001001200000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000700000000000000000000000000003803f00000000000000000000000000000000040000006009000000000000000000200000000000000000000000000000000002000000a004800000000000000000100000000000000000000000000000000001000000c0024000000000000000000800000000000000000000000000000000008000000c0120000000000000000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 256. -/
noncomputable def allowed256 : List Nat := [0x1,0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 256. -/
noncomputable def tree256 : ParitySearchTree := (.split 0 .done (.split 1 .done (.split 2 (.pack [0]) (.split 3 (.pack [1]) (.split 4 (.pack [2]) (.split 5 (.pack [3]) (.split 15 (.pack [5]) (.split 16 (.pack [6]) (.split 17 (.pack [7]) (.split 132 (.pack [9]) (.split 133 (.pack [10]) (.split 134 (.pack [8]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 256. -/
theorem checked256 : checkParitySearch 8 (fun q => (rows256 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed256.contains) tree256 0xfff9ffffffffffffff0e7ee7fe7fc4ffcffffffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 257. -/
noncomputable def rows257 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000400800140140000000180000030034000402400000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000008008c01801800800800b00020010106002012000004000000000000000000000400800740180000800080000130008018401200000004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 257. -/
noncomputable def allowed257 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 257. -/
noncomputable def tree257 : ParitySearchTree := (.split 34 (.pack [2]) (.split 37 (.pack [4]) (.split 46 (.pack [5]) (.split 62 (.pack [10]) (.split 64 (.pack [11]) (.split 65 (.pack [9]) (.split 76 .done (.split 77 (.pack [12]) (.split 103 (.pack [1]) (.split 104 (.pack [0]) (.split 138 (.pack [7]) (.split 140 (.pack [1]) (.split 150 (.pack [8]) (.split 152 (.pack [3]) (.split 167 (.pack [7]) (.split 178 (.pack [12]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 257. -/
theorem checked257 : checkParitySearch 8 (fun q => (rows257 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed257.contains) tree257 0xfff9fffffffffffbeffb7f27ff5ffcffcffffffffa5ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 258. -/
noncomputable def rows258 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000004008001401400000001800000300340004024000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000004006800200cc0160090000000000020010030

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 258. -/
noncomputable def allowed258 : List Nat := [0x10000000000000000000,0x80000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 258. -/
noncomputable def tree258 : ParitySearchTree := (.split 34 (.pack [3]) (.split 37 (.pack [5]) (.split 46 (.pack [6]) (.split 62 (.pack [11]) (.split 64 (.pack [12]) (.split 65 (.pack [10]) (.split 76 .done (.split 77 (.pack [13]) (.split 103 .done (.split 104 (.pack [0]) (.split 138 (.pack [1]) (.split 140 (.pack [2]) (.split 150 (.pack [9]) (.split 152 (.pack [4]) (.split 167 (.pack [8]) (.split 178 (.pack [13]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 258. -/
theorem checked258 : checkParitySearch 8 (fun q => (rows258 >>> (256*q)) &&& (2^256-1)) 0x81 (allowed258.contains) tree258 0xfff9fffffffffffb7fde7f67ff7ff4ffcffffffffaff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 259. -/
noncomputable def rows259 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000400800140140000000180000030034000402400000000000000000000000000020080018018000000014000002802c000201200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000000008000000c0020000000000000000004004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 259. -/
noncomputable def allowed259 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 259. -/
noncomputable def tree259 : ParitySearchTree := (.split 34 (.pack [1]) (.split 37 (.pack [3]) (.split 46 (.pack [4]) (.split 62 (.pack [10]) (.split 64 (.pack [11]) (.split 65 (.pack [9]) (.split 76 .done (.split 77 (.pack [12]) (.split 103 (.pack [0]) (.split 104 (.pack [5]) (.split 138 (.pack [7]) (.split 140 (.pack [5]) (.split 150 (.pack [8]) (.split 152 (.pack [2]) (.split 167 (.pack [7]) (.split 178 (.pack [12]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 259. -/
theorem checked259 : checkParitySearch 8 (fun q => (rows259 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed259.contains) tree259 0xfff9fffffffffff9afff7f27ffdffcffcffffffffc5ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 260. -/
noncomputable def rows260 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000400800140140000000180000030034000402400000000000000000000000000020080018018000000014000002802c0002012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000008000000c0020000000000000000004004

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 260. -/
noncomputable def allowed260 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 260. -/
noncomputable def tree260 : ParitySearchTree := (.split 34 (.pack [2]) (.split 37 (.pack [4]) (.split 46 (.pack [5]) (.split 62 (.pack [11]) (.split 64 (.pack [12]) (.split 65 (.pack [10]) (.split 76 .done (.split 77 (.pack [13]) (.split 103 (.pack [0]) (.split 104 (.pack [6]) (.split 138 (.pack [1]) (.split 140 (.pack [6]) (.split 150 (.pack [9]) (.split 152 (.pack [3]) (.split 167 (.pack [8]) (.split 178 (.pack [13]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 260. -/
theorem checked260 : checkParitySearch 8 (fun q => (rows260 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed260.contains) tree260 0xfff9fffffffffff977feff27ffeffcffcffffffffc3ff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 261. -/
noncomputable def rows261 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000002000800a001400000001800000300260100024000000000000000000000000002000800ac018000010008002003400101060120000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000400000300090000000000000000002000000000000000000000004805000d800004005404800380050a6008200000002

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 261. -/
noncomputable def allowed261 : List Nat := [0x10000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 261. -/
noncomputable def tree261 : ParitySearchTree := (.split 22 (.pack [3]) (.split 25 (.pack [4]) (.split 40 (.pack [9]) (.split 49 (.pack [12]) (.split 50 (.pack [10]) (.split 53 (.pack [13]) (.split 64 .done (.split 65 (.pack [14]) (.split 91 (.pack [0]) (.split 92 (.pack [6]) (.split 126 (.pack [1]) (.split 128 (.pack [2]) (.split 141 (.pack [11]) (.split 143 (.pack [5]) (.split 155 (.pack [8]) (.split 169 (.pack [14]) (.zero 7)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 261. -/
theorem checked261 : checkParitySearch 8 (fun q => (rows261 >>> (256*q)) &&& (2^256-1)) 0xc0 (allowed261.contains) tree261 0xfff9ff9ffffffffffdf7fdbff3ff77fe7ffcfffffffd2 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 262. -/
noncomputable def rows262 : Nat := 0x3000000000000000800000100120000000000000000000000000000000000000500000000000000040000008009000000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000002000800a001400000001800000300260100024000000000000000000000000002000800ac018000010008002003400101060120000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 262. -/
noncomputable def allowed262 : List Nat := [0x80000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 262. -/
noncomputable def tree262 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [3]) (.split 40 (.pack [8]) (.split 49 (.pack [11]) (.split 50 (.pack [9]) (.split 53 (.pack [12]) (.split 64 (.pack [13]) (.split 65 (.pack [14]) (.split 91 .done (.split 92 (.pack [5]) (.split 126 (.pack [0]) (.split 128 (.pack [1]) (.split 141 (.pack [10]) (.split 143 (.pack [4]) (.split 155 (.pack [7]) (.split 169 (.pack [14]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 262. -/
theorem checked262 : checkParitySearch 8 (fun q => (rows262 >>> (256*q)) &&& (2^256-1)) 0x60 (allowed262.contains) tree262 0xfff9ff9fffffffdbfff7f9bffbfff7fe7ffcffffd7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 263. -/
noncomputable def rows263 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000000000c000000010000002002400300360000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000005a00000b4000000000000000000002d028a0000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000a00000000800c00040180020012000000000004002806

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 263. -/
noncomputable def allowed263 : List Nat := [0x10000000000000000000,0x80000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 263. -/
noncomputable def tree263 : ParitySearchTree := (.split 1 (.pack [1]) (.split 2 (.pack [2]) (.split 11 (.pack [3]) (.split 13 (.pack [4]) (.split 26 (.pack [6]) (.split 73 (.pack [10]) (.split 76 .done (.split 89 (.pack [11]) (.split 103 .done (.split 104 (.pack [7]) (.split 114 (.pack [4]) (.split 130 (.pack [6]) (.split 131 (.pack [5]) (.split 143 (.pack [8]) (.split 177 (.pack [11]) (.split 179 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 263. -/
theorem checked263 : checkParitySearch 8 (fun q => (rows263 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed263.contains) tree263 0xfff9ff6ffefffffb7ffa7f27ff7ffcfffffffff7fafff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 264. -/
noncomputable def rows264 : Nat := 0x600000000000000100000020024000000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000000000c0000000100000020024003003600000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000007e0000000000000000000000000003f038e0000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00200000000000000000040040000000000000000000a00000000c00400100140000012000000000006004c02

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 264. -/
noncomputable def allowed264 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 264. -/
noncomputable def tree264 : ParitySearchTree := (.split 1 (.pack [2]) (.split 10 (.pack [3]) (.split 11 (.pack [4]) (.split 14 (.pack [1]) (.split 25 (.pack [5]) (.split 26 (.pack [6]) (.split 73 (.pack [10]) (.split 76 .done (.split 102 (.pack [1]) (.split 104 (.pack [7]) (.split 116 (.pack [11]) (.split 130 (.pack [6]) (.split 142 (.pack [8]) (.split 143 (.pack [8]) (.split 177 (.pack [11]) (.split 179 (.pack [9]) (.zero 0)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 264. -/
theorem checked264 : checkParitySearch 8 (fun q => (rows264 >>> (256*q)) &&& (2^256-1)) 0x1 (allowed264.contains) tree264 0xfff9ff6ffefffff93ffe7f27fffffcfffffffff7fcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 265. -/
noncomputable def rows265 : Nat := 0x300000000000000080000010012000000000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000006000200c0014000000010000002001403400240000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000004002000400c0018000080000010010002c008001200000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000a0000080080010006011802f012000000004000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 265. -/
noncomputable def allowed265 : List Nat := [0x10000000000000,0x200000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 265. -/
noncomputable def tree265 : ParitySearchTree := (.split 22 (.pack [2]) (.split 25 (.pack [4]) (.split 38 (.pack [7]) (.split 40 (.pack [8]) (.split 41 (.pack [9]) (.split 50 (.pack [10]) (.split 52 .done (.split 65 (.pack [11]) (.split 92 (.pack [0]) (.split 126 (.pack [7]) (.split 128 (.pack [1]) (.split 142 (.pack [4]) (.split 143 (.pack [5]) (.split 153 .done (.split 169 (.pack [11]) (.split 170 (.pack [3]) (.zero 6)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 265. -/
theorem checked265 : checkParitySearch 8 (fun q => (rows265 >>> (256*q)) &&& (2^256-1)) 0x41 (allowed265.contains) tree265 0xfff9febffdffffffffdbf97ff3ffeffd7ffcffefffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 266. -/
noncomputable def rows266 : Nat := 0xa000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000005000400a0018000000010000002000c02c0012000000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000040000014001000000000000000000200200000000000000000000000000000001000000180240000000000000000008000000000000000000000000000c000008008001000a01180370090000000040000000000000000000000005000c000048004003001200280a7009000000024022

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 266. -/
noncomputable def allowed266 : List Nat := [0x10000000000000000,0x80000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 266. -/
noncomputable def tree266 : ParitySearchTree := (.split 14 (.pack [4]) (.split 48 (.pack [9]) (.split 51 (.pack [6]) (.split 60 (.pack [9]) (.split 61 (.pack [10]) (.split 62 (.pack [11]) (.split 64 .done (.split 65 (.pack [12]) (.split 75 (.pack [13]) (.split 76 (.pack [14]) (.split 80 (.pack [12]) (.split 89 (.pack [2]) (.split 91 .done (.split 104 (.pack [3]) (.split 119 (.pack [5]) (.split 131 (.pack [8]) (.split 154 (.pack [0]) (.split 155 (.pack [7]) (.zero 1)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 266. -/
theorem checked266 : checkParitySearch 8 (fun q => (rows266 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed266.contains) tree266 0xfff9fddffbffffffffb7f9bff3fff7fcfffcffdfffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 267. -/
noncomputable def rows267 : Nat := 0x1800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000080000060000000000000000000000400480000000000000000000000006000400800140140000000000000030034000402400000000000000000000000000000002000000300000000000000000000010012000000000000000000000000000000000040000008009001c01f8000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 267. -/
noncomputable def allowed267 : List Nat := [0x10000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 267. -/
noncomputable def tree267 : ParitySearchTree := (.split 5 (.pack [1]) (.split 51 (.pack [4]) (.split 52 .done (.split 53 (.pack [5]) (.split 54 (.pack [6]) (.split 55 (.pack [7]) (.split 56 (.pack [8]) (.split 66 (.pack [10]) (.split 67 (.pack [11]) (.split 68 (.pack [9]) (.split 80 (.pack [9]) (.split 83 (.pack [12]) (.split 95 (.pack [2]) (.split 122 (.pack [3]) (.zero 0)))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 267. -/
theorem checked267 : checkParitySearch 8 (fun q => (rows267 >>> (256*q)) &&& (2^256-1)) 0x5 (allowed267.contains) tree267 0xfff9fcfff9ffffffffdbf97ff3ffeffffffcffcfffff9 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 268. -/
noncomputable def rows268 : Nat := 0x30000000000000008000001001200000000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000030000006000c000000010000002003c018003600000000000000000000000000000000400000060000000000000000000002002400000000000000000000000020000002001800c0000180000030026014002c04800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000001000000180240000000000000000008000000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 268. -/
noncomputable def allowed268 : List Nat := [0x10000000000000000,0x80000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 268. -/
noncomputable def tree268 : ParitySearchTree := (.split 11 (.pack [1]) (.split 14 (.pack [7]) (.split 22 (.pack [2]) (.split 23 (.pack [3]) (.split 25 (.pack [5]) (.split 38 (.pack [10]) (.split 40 (.pack [9]) (.split 49 (.pack [12]) (.split 50 (.pack [10]) (.split 53 (.pack [11]) (.split 64 .done (.split 65 (.pack [13]) (.split 91 .done (.split 92 (.pack [8]) (.split 114 (.pack [5]) (.split 115 (.pack [4]) (.split 127 (.pack [0]) (.split 128 (.pack [1]) (.split 141 (.pack [11]) (.split 169 (.pack [13]) (.zero 6)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 268. -/
theorem checked268 : checkParitySearch 8 (fun q => (rows268 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed268.contains) tree268 0xfff9fb1ff7ffffffffb7f9bff3fff7fffffcffbfffffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 269. -/
noncomputable def rows269 : Nat := 0x140000000000000010000002002400000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000001400000000000000100000020024000000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000000004004803003600000000000000000020000020800000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000000008000002801200000000000000000040000000000000000000000c00f000000002002002500080040458000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000004000000600900000000000000000020

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 269. -/
noncomputable def allowed269 : List Nat := [0x4000000000000000,0x80000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 269. -/
noncomputable def tree269 : ParitySearchTree := (.split 8 (.pack [4]) (.split 55 (.pack [8]) (.split 56 (.pack [9]) (.split 58 (.pack [11]) (.split 62 .done (.split 70 (.pack [12]) (.split 83 (.pack [0]) (.split 96 (.pack [1]) (.split 98 (.pack [1]) (.split 101 (.pack [3]) (.split 113 (.pack [5]) (.split 125 (.pack [6]) (.split 160 (.pack [10]) (.split 161 (.pack [10]) (.split 162 (.pack [11]) (.split 163 .done (.split 174 (.pack [13]) (.split 175 (.pack [7]) (.zero 2)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 269. -/
theorem checked269 : checkParitySearch 8 (fun q => (rows269 >>> (256*q)) &&& (2^256-1)) 0x4 (allowed269.contains) tree269 0xfff9f7f7fff7fffffff7dfd2ffaffe7ff7ff9bffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 270. -/
noncomputable def rows270 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000006000000c00000000001c000003803c00360000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 270. -/
noncomputable def allowed270 : List Nat := [0x200000000000,0x400000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 270. -/
noncomputable def tree270 : ParitySearchTree := (.split 45 .done (.split 46 .done (.split 48 (.pack [8]) (.split 49 (.pack [9]) (.split 62 (.pack [11]) (.split 63 (.pack [8]) (.split 64 (.pack [9]) (.split 65 (.pack [10]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.split 150 (.pack [7]) (.split 151 (.pack [7]) (.split 177 (.pack [12]) (.split 178 (.pack [12]) (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 270. -/
theorem checked270 : checkParitySearch 8 (fun q => (rows270 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed270.contains) tree270 0xfff9e7edffc7fffffffffffffffffc9fffff93fe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 271. -/
noncomputable def rows271 : Nat := (Nat.lor 0x2000001800000000000000000000010012000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000006000000074008000400c000002400000000003a03940400000000000000000000000000000000800000280120000000000000000004000000000000000000000a000000048000002400001500820000000000240208020000000000000000000000800a00140000200040100040019010002400000001 (Nat.shiftLeft 0xc0000000000000020000004004800000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 271. -/
noncomputable def allowed271 : List Nat := [0x1000,0x20000000000000000000,0x80000000000000000000000000,0x400000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 271. -/
noncomputable def tree271 : ParitySearchTree := (.split 2 (.pack [6]) (.split 10 (.pack [2]) (.split 12 .done (.split 15 (.pack [4]) (.split 16 (.pack [5]) (.split 17 (.pack [6]) (.split 25 (.pack [7]) (.split 27 (.pack [8]) (.split 28 (.pack [9]) (.split 29 (.pack [10]) (.split 74 (.pack [16]) (.split 77 .done (.split 102 (.pack [0]) (.split 103 .done (.split 114 (.pack [1]) (.split 131 (.pack [9]) (.split 142 (.pack [11]) (.split 144 (.pack [13]) (.split 145 (.pack [14]) (.split 146 (.pack [12]) (.split 177 (.pack [15]) (.split 178 .done (.zero 3)))))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 271. -/
theorem checked271 : checkParitySearch 8 (fun q => (rows271 >>> (256*q)) &&& (2^256-1)) 0x8 (allowed271.contains) tree271 0xfff9bffbfffffff27feeff57fe7ffbffdfffdffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 272. -/
noncomputable def rows272 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000000000000000000000007007e0000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000040000030000000000000000000000200240000000000000000000000000000000008000002801200000000000000000040000000000000000000006009000009b00400000a0011009010401201044004a000000000000000000000000000002000000000000140168000000000010012005

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 272. -/
noncomputable def allowed272 : List Nat := [0x1000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 272. -/
noncomputable def tree272 : ParitySearchTree := (.split 9 (.pack [3]) (.split 10 (.pack [2]) (.split 11 (.pack [4]) (.split 12 .done (.split 13 (.pack [0]) (.split 14 (.pack [1]) (.split 24 (.pack [6]) (.split 25 (.pack [7]) (.split 26 (.pack [8]) (.split 141 (.pack [10]) (.split 142 (.pack [11]) (.split 143 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 272. -/
theorem checked272 : checkParitySearch 8 (fun q => (rows272 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed272.contains) tree272 0xfff9bffbfffffff03feaff57fefffbffdfffdffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 273. -/
noncomputable def rows273 : Nat := 0xa00000000000000080000010012000000000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000000002000000a00000000000000000000010012000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000a0090010019003000614000002802800420190020004800000000000000000000000000000004000001400100000000000000000020020000000000000000000c0018000000020004004800003003e200000000001001000000000000000000000000000000008000002801200000000000000000040000000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 273. -/
noncomputable def allowed273 : List Nat := [0x4000000000000000,0x80000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 273. -/
noncomputable def tree273 : ParitySearchTree := (.split 0 (.pack [0]) (.split 12 (.pack [7]) (.split 57 (.pack [14]) (.split 61 (.pack [10]) (.split 62 .done (.split 63 (.pack [11]) (.split 64 (.pack [12]) (.split 65 (.pack [13]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 99 (.pack [3]) (.split 102 (.pack [5]) (.split 114 (.pack [8]) (.split 129 (.pack [9]) (.split 163 .done (.split 164 (.pack [6]) (.split 178 (.pack [10]) (.split 179 (.pack [15]) (.zero 4)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 273. -/
theorem checked273 : checkParitySearch 8 (fun q => (rows273 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed273.contains) tree273 0xfff9bff77ff7fffffff7dfd2ffaffebff7ff9fffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 274. -/
noncomputable def rows274 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000006000000c00000000001c000003803c00360000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 274. -/
noncomputable def allowed274 : List Nat := [0x200000000000,0x400000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 274. -/
noncomputable def tree274 : ParitySearchTree := (.split 45 .done (.split 46 .done (.split 48 (.pack [8]) (.split 49 (.pack [9]) (.split 62 (.pack [7]) (.split 63 (.pack [8]) (.split 64 (.pack [9]) (.split 65 (.pack [10]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.split 150 (.pack [7]) (.split 151 (.pack [7]) (.split 177 (.pack [11]) (.split 178 (.pack [11]) (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 274. -/
theorem checked274 : checkParitySearch 8 (fun q => (rows274 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed274.contains) tree274 0xfff9afed7fc7fffffffffffffffffc5fffff97fe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 275. -/
noncomputable def rows275 : Nat := 0x1400000000000000100000020024000000000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000000400000060000000000000000000002002400000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000002000000a000000000000000000000100120000000000000000000a00000000c00400100140000012000000000006004c02000000000000000000060090000096808000006000a012008202402084004c000000000000000000000c00000002400000900000188041000000000012010401

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 275. -/
noncomputable def allowed275 : List Nat := [0x4000,0x10000000000000000000,0x40000000000000000000000000,0x200000000000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 275. -/
noncomputable def tree275 : ParitySearchTree := (.split 1 (.pack [3]) (.split 10 (.pack [4]) (.split 11 (.pack [5]) (.split 14 .done (.split 25 (.pack [6]) (.split 26 (.pack [7]) (.split 73 (.pack [10]) (.split 76 .done (.split 102 .done (.split 104 (.pack [1]) (.split 116 (.pack [0]) (.split 130 (.pack [8]) (.split 142 (.pack [9]) (.split 143 (.pack [9]) (.split 177 .done (.split 179 (.pack [0]) (.zero 2)))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 275. -/
theorem checked275 : checkParitySearch 8 (fun q => (rows275 >>> (256*q)) &&& (2^256-1)) 0x6 (allowed275.contains) tree275 0xfff97ff7fffffff93ff77f8ffd7ffbffefffbffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 276. -/
noncomputable def rows276 : Nat := 0x40000006000000000000000000000200240000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000000e00000000000000000000000000007007e00000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000800000280000000000000000000004004800000000000000000000a0090000056810000005000c024008202402082002c00000000000000000000000000000000004000003000900000000000000000020000000000000000000000000000060000000000001801b0000000000030036006

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 276. -/
noncomputable def allowed276 : List Nat := [0x4000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 276. -/
noncomputable def tree276 : ParitySearchTree := (.split 9 (.pack [1]) (.split 10 (.pack [3]) (.split 11 (.pack [4]) (.split 12 (.pack [0]) (.split 13 (.pack [2]) (.split 14 .done (.split 24 (.pack [6]) (.split 25 (.pack [7]) (.split 26 (.pack [8]) (.split 141 (.pack [10]) (.split 142 (.pack [11]) (.split 143 (.pack [9]) (.zero 5)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 276. -/
theorem checked276 : checkParitySearch 8 (fun q => (rows276 >>> (256*q)) &&& (2^256-1)) 0x21 (allowed276.contains) tree276 0xfff97ff7fffffff03fe77f8fff7ffbffefffbffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 277. -/
noncomputable def rows277 : Nat := 0x60000000000000010000002002400000000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000006000000c00000000001c000003803c00360000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 277. -/
noncomputable def allowed277 : List Nat := [0x200000000000,0x400000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 277. -/
noncomputable def tree277 : ParitySearchTree := (.split 45 .done (.split 46 .done (.split 48 (.pack [8]) (.split 49 (.pack [9]) (.split 62 (.pack [7]) (.split 63 (.pack [8]) (.split 64 (.pack [9]) (.split 65 (.pack [10]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.split 150 (.pack [7]) (.split 151 (.pack [7]) (.split 177 (.pack [11]) (.split 178 (.pack [11]) (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 277. -/
theorem checked277 : checkParitySearch 8 (fun q => (rows277 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed277.contains) tree277 0xfff977ecffc7fffffffffffffffffc3fffff9bfe3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 278. -/
noncomputable def rows278 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000001c0000000000000000000000000000e00fc00000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000001000000500000000000000000000008009000000000000000000000000000000080000060000000000000000000000400480000000000000000000000000080000000000005000000000000000400480140168000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 278. -/
noncomputable def allowed278 : List Nat := [0x200000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 278. -/
noncomputable def tree278 : ParitySearchTree := (.split 42 (.pack [1]) (.split 43 (.pack [2]) (.split 44 (.pack [3]) (.split 45 .done (.split 46 (.pack [0]) (.split 47 (.pack [5]) (.split 57 (.pack [6]) (.split 58 (.pack [7]) (.split 59 (.pack [8]) (.split 174 (.pack [10]) (.split 175 (.pack [10]) (.split 176 (.pack [9]) (.zero 4)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 278. -/
theorem checked278 : checkParitySearch 8 (fun q => (rows278 >>> (256*q)) &&& (2^256-1)) 0x10 (allowed278.contains) tree278 0xfff93fec7f57ffdffdffffffbffffcffffff3fff7ff7f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 279. -/
noncomputable def rows279 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 279. -/
noncomputable def allowed279 : List Nat := [0x200000000000000,0x400000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 279. -/
noncomputable def tree279 : ParitySearchTree := (.split 54 (.pack [3]) (.split 55 (.pack [4]) (.split 56 (.pack [5]) (.split 57 .done (.split 58 .done (.split 59 (.pack [7]) (.split 69 (.pack [8]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 279. -/
theorem checked279 : checkParitySearch 8 (fun q => (rows279 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed279.contains) tree279 0xfff8c7fdffe7fffffffffffffffffcfff9ff83ff3ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 280. -/
noncomputable def rows280 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 280. -/
noncomputable def allowed280 : List Nat := [0x200000000000000,0x400000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 280. -/
noncomputable def tree280 : ParitySearchTree := (.split 54 (.pack [3]) (.split 55 (.pack [4]) (.split 56 (.pack [5]) (.split 57 .done (.split 58 .done (.split 59 (.pack [7]) (.split 69 (.pack [8]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 280. -/
theorem checked280 : checkParitySearch 8 (fun q => (rows280 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed280.contains) tree280 0xfff8c7f97feffffffffffffffffffcfff5ff83ff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 281. -/
noncomputable def rows281 : Nat := 0x180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000c00000000000000200000040048000000000000000000000000000000000000000000000000000007000000e00fc0000000000000000000000000000000000000300000000000000080000010012000000000000000000000000000000000000050000000000000004000000800900000000000000000000000000000000000006000000000000000200000040048000000000000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 281. -/
noncomputable def allowed281 : List Nat := [0x200000000000000,0x400000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 281. -/
noncomputable def tree281 : ParitySearchTree := (.split 54 (.pack [3]) (.split 55 (.pack [4]) (.split 56 (.pack [5]) (.split 57 .done (.split 58 .done (.split 59 (.pack [7]) (.split 69 (.pack [8]) (.split 70 (.pack [9]) (.split 71 (.pack [10]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 281. -/
theorem checked281 : checkParitySearch 8 (fun q => (rows281 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed281.contains) tree281 0xfff8c7f4fff7fffffffffffffffffcfff3ff83ffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 282. -/
noncomputable def rows282 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e00000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 282. -/
noncomputable def allowed282 : List Nat := [0x1000000000000000,0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 282. -/
noncomputable def tree282 : ParitySearchTree := (.split 57 (.pack [3]) (.split 58 (.pack [4]) (.split 59 (.pack [5]) (.split 60 .done (.split 61 .done (.split 62 .done (.split 72 (.pack [7]) (.split 73 (.pack [8]) (.split 74 (.pack [9]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 282. -/
theorem checked282 : checkParitySearch 8 (fun q => (rows282 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed282.contains) tree282 0xfff83f63fffffffffffff6fff3ffe7fdfffb1ffffffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 283. -/
noncomputable def rows283 : Nat := (Nat.lor 0x60000000000000002000000400480000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000080000028012000000000000000000400000000000000000000000000000000004000003000900000000000000000020000000000000000000000002004000c00c040008010008001a00d00080480000200000000000000000000004002000c00c0200040100040019016000804800001 (Nat.shiftLeft 0x5000000000000000400000080090000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 283. -/
noncomputable def allowed283 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 283. -/
noncomputable def tree283 : ParitySearchTree := (.split 1 .done (.split 23 (.pack [6]) (.split 26 (.pack [10]) (.split 35 (.pack [8]) (.split 48 (.pack [11]) (.split 50 (.pack [12]) (.split 51 (.pack [13]) (.split 61 (.pack [14]) (.split 63 (.pack [15]) (.split 64 (.pack [16]) (.split 79 (.pack [16]) (.split 92 (.pack [0]) (.split 103 (.pack [4]) (.split 118 (.pack [7]) (.split 126 (.pack [2]) (.split 127 (.pack [3]) (.split 138 (.pack [5]) (.split 139 (.pack [11]) (.split 154 (.pack [9]) (.split 165 (.pack [11]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 283. -/
theorem checked283 : checkParitySearch 8 (fun q => (rows283 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed283.contains) tree283 0xfff7ff7fffffffcf3f6ff73ffe7fdffdfffbffffe4fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 284. -/
noncomputable def rows284 : Nat := 0x500000000000000040000008009000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000004000003000000000000000000000020024000000000000000000000042006006c040000000011002800d0000208000020020000000000000000000000000000000080000028012000000000000000000400000000000000000000000000000000004000003000900000000000000000020000000000000000000000002004000c00c040008010008001a00d0008048000020000000000000000000a002002048c00c044008011004a002016000820820801

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 284. -/
noncomputable def allowed284 : List Nat := [0x2]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 284. -/
noncomputable def tree284 : ParitySearchTree := (.split 1 .done (.split 23 (.pack [6]) (.split 26 (.pack [9]) (.split 35 (.pack [7]) (.split 48 (.pack [10]) (.split 50 (.pack [11]) (.split 51 (.pack [12]) (.split 61 (.pack [13]) (.split 63 (.pack [14]) (.split 64 (.pack [15]) (.split 79 (.pack [15]) (.split 92 (.pack [0]) (.split 103 (.pack [4]) (.split 118 (.pack [4]) (.split 126 (.pack [2]) (.split 127 (.pack [3]) (.split 138 (.pack [5]) (.split 139 (.pack [10]) (.split 154 (.pack [8]) (.split 165 (.pack [10]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 284. -/
theorem checked284 : checkParitySearch 8 (fun q => (rows284 >>> (256*q)) &&& (2^256-1)) 0x12 (allowed284.contains) tree284 0xfff7ff7fffffffcd7f6bf73ffeffdffdfffbffffe2fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 285. -/
noncomputable def rows285 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000004000000600000000000000000000020024000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000080000028000000000000000000000400480000000000000000000000000000004000003000000000000000000000020024000000000000000000000042006006c040000000011002800d0000208000020020000000000000000000000000000000080000028012000000000000000000400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 285. -/
noncomputable def allowed285 : List Nat := [0x2,0x100000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 285. -/
noncomputable def tree285 : ParitySearchTree := (.split 1 .done (.split 13 (.pack [5]) (.split 35 (.pack [6]) (.split 41 (.pack [9]) (.split 60 (.pack [11]) (.split 62 (.pack [12]) (.split 63 (.pack [13]) (.split 75 (.pack [14]) (.split 77 (.pack [15]) (.split 88 (.pack [0]) (.split 92 .done (.split 130 (.pack [9]) (.split 138 (.pack [2]) (.split 139 (.pack [3]) (.split 141 (.pack [4]) (.split 142 (.pack [5]) (.split 153 (.pack [7]) (.split 154 (.pack [8]) (.split 165 (.pack [10]) (.split 170 (.pack [13]) (.zero 1)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 285. -/
theorem checked285 : checkParitySearch 8 (fun q => (rows285 >>> (256*q)) &&& (2^256-1)) 0x2 (allowed285.contains) tree285 0xfff7ff7fffffffc9ff2bf7bfffffcffdfffbffffe7ffa 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 286. -/
noncomputable def rows286 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000020000003000000000000000000000100120000000000000000000000000000018001003001d000000020000004004400b00650000000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000100000000018003000020000004004000f006000d80000000000000000000000000000002000000a000000000000000000000100120000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000800000600000000000000000000004004800000000000000000000002000200cc003003690000012010404a042400001040000000000000000000000000000001000000c0000000000000000000000800900000000000000000000000000000000400000300090000000000000000002000000000000000000000000080010008001003000600900000000400400190100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 286. -/
noncomputable def allowed286 : List Nat := [0x40000000,0x400000000000000,0x4000000000000000000000000000000000,0x20000000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 286. -/
noncomputable def tree286 : ParitySearchTree := (.split 28 (.pack [6]) (.split 30 .done (.split 33 (.pack [8]) (.split 34 (.pack [9]) (.split 44 (.pack [11]) (.split 45 (.pack [7]) (.split 47 (.pack [12]) (.split 58 .done (.split 62 (.pack [12]) (.split 74 (.pack [14]) (.split 101 (.pack [1]) (.split 132 (.pack [2]) (.split 134 .done (.split 135 (.pack [4]) (.split 136 (.pack [5]) (.split 148 (.pack [0]) (.split 149 .done (.split 160 (.pack [3]) (.split 175 (.pack [14]) (.split 176 (.pack [13]) (.zero 10)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 286. -/
theorem checked286 : checkParitySearch 8 (fun q => (rows286 >>> (256*q)) &&& (2^256-1)) 0x408 (allowed286.contains) tree286 0xfff797ef3fdfffbffffffffffffffc5fff3f67ffdffdf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 287. -/
noncomputable def rows287 : Nat := 0x18000000000000004000000800900000000000000000000000000000000000002800000000000000200000040048000000000000000000000000000000000000300000000000000010000002002400000000000000000000000000000000000000000000000000000007000000e00fc000000000000000000000000000000000000030000000000000008000001001200000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000000180000000200000040048006006c00000000000000000000000000010000021006003600006000000c00d00110090104000000000000000000000000000000000002000000300480000000000000000010000000000000000000000000000000000100000050024000000000000000000800000000000000000000000000000000008000006001200000000000000000040

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 287. -/
noncomputable def allowed287 : List Nat := [0x400000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 287. -/
noncomputable def tree287 : ParitySearchTree := (.split 54 (.pack [5]) (.split 55 (.pack [6]) (.split 56 (.pack [7]) (.split 57 (.pack [3]) (.split 58 .done (.split 59 (.pack [4]) (.split 69 (.pack [9]) (.split 70 (.pack [10]) (.split 71 (.pack [11]) (.split 96 (.pack [1]) (.split 97 (.pack [2]) (.split 98 (.pack [0]) (.zero 8)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 287. -/
theorem checked287 : checkParitySearch 8 (fun q => (rows287 >>> (256*q)) &&& (2^256-1)) 0x108 (allowed287.contains) tree287 0xfff707ee3fdfffbffffffffffffffcffff3f6fffdffdf 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 288. -/
noncomputable def rows288 : Nat := 0xc00000000000000200000040048000000000000000000000000000000000000140000000000000010000002002400000000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000010000005000000000000000000000080090000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000400000300000000000000000000002002400000000000000000000000080080000000005000010000002002000a80e80168000000000000000000000000008000000000000500000000000000040048014016800000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000001000000c00000000000000000000008009000000000000000000000000000000004000003000900000000000000000020000000000000000000000000000000000040000006009000000000000000000200000000000000000000028180020010001001000a00080480000c00c800201300000000000000000000000000000000001000000c00240000000000000000008

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 288. -/
noncomputable def allowed288 : List Nat := [0x200000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 288. -/
noncomputable def tree288 : ParitySearchTree := (.split 15 (.pack [4]) (.split 17 (.pack [5]) (.split 18 (.pack [8]) (.split 20 (.pack [9]) (.split 31 (.pack [10]) (.split 33 (.pack [8]) (.split 34 (.pack [11]) (.split 35 (.pack [9]) (.split 43 (.pack [10]) (.split 45 .done (.split 47 (.pack [1]) (.split 61 (.pack [12]) (.split 73 (.pack [13]) (.split 100 (.pack [3]) (.split 120 (.pack [0]) (.split 122 (.pack [2]) (.split 163 (.pack [6]) (.split 175 (.pack [14]) (.zero 7)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 288. -/
theorem checked288 : checkParitySearch 8 (fun q => (rows288 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed288.contains) tree288 0xfff59ff67f57ffdffdffffffbffffa9fffffefff7ff7f 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 289. -/
noncomputable def rows289 : Nat := (Nat.lor 0x3000000000000000100000020024000000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000000008000000c00000000000000000000040048000000000000000000000000000000200000180000000000000000000001001200000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000000800000280000000000000000000004004800000000000000000000000000000040000030000000000000000000000200240000000000000000000000000010006001801b08000001001200500520000082000000000000000000000000000000040000006000000000000000000000200240000000000000000000000000000000200000180008000000000000000001001000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000080000060012000000000000000000400000000000000000000000000000000000400000140090000000000000000002 (Nat.shiftLeft 0x28000000000000002000000400480000000000000000 4096))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 289. -/
noncomputable def allowed289 : List Nat := [0x20000000000000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 289. -/
noncomputable def tree289 : ParitySearchTree := (.split 5 (.pack [4]) (.split 11 (.pack [2]) (.split 33 (.pack [8]) (.split 36 (.pack [9]) (.split 38 (.pack [10]) (.split 48 (.pack [12]) (.split 50 (.pack [14]) (.split 61 (.pack [11]) (.split 64 (.pack [13]) (.split 76 (.pack [0]) (.split 103 (.pack [3]) (.split 108 (.pack [15]) (.split 109 (.pack [16]) (.split 111 (.pack [7]) (.split 112 (.pack [6]) (.split 123 (.pack [1]) (.split 124 (.pack [8]) (.split 137 .done (.split 138 (.pack [6]) (.split 152 (.pack [11]) (.zero 5)))))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 289. -/
theorem checked289 : checkParitySearch 8 (fun q => (rows289 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed289.contains) tree289 0xfff4bffd7ef7ffbffbffffff7ffffafff5ff3ffe7feff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 290. -/
noncomputable def rows290 : Nat := 0x1c000003803f000000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 290. -/
noncomputable def allowed290 : List Nat := [0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 290. -/
noncomputable def tree290 : ParitySearchTree := (.split 60 (.pack [9]) (.split 61 .done (.split 62 .done (.split 63 (.pack [6]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.zero 10)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 290. -/
theorem checked290 : checkParitySearch 8 (fun q => (rows290 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed290.contains) tree290 0xfff18ff2ffdfffffffffffffffffff3ff9ff07fefffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 291. -/
noncomputable def rows291 : Nat := 0x1c000003803f000000000000000000000000000000000000018000000000000000800000100120000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 291. -/
noncomputable def allowed291 : List Nat := [0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 291. -/
noncomputable def tree291 : ParitySearchTree := (.split 60 (.pack [9]) (.split 61 .done (.split 62 .done (.split 63 (.pack [6]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.zero 10)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 291. -/
theorem checked291 : checkParitySearch 8 (fun q => (rows291 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed291.contains) tree291 0xfff18fe9ffefffffffffffffffffff3ff5ff07ff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 292. -/
noncomputable def rows292 : Nat := 0xa0000000000000008000001001200000000000000000000000000000000000000060000000000000002000000400480000000000000000000000000000000000000000a00000000000000080000010012000000000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000004000001400000000000000000000020024000000000000000000000000000000100000018000000000000000000000800900000000000000000000000080000004018002800004000000800d00280680048000000000000000000000000000000400000300000000000000000000002002400000000000000000000000000000000100000018000000000000000000000800900000000000000000000000000000008000002800000000000000000000040048000000000000000000000000000000100000050000000000000000000000800900000000000000000000000140000000080000000012005005a000000000004000000000000000000000000000000000020000003004800000000000000000100

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 292. -/
noncomputable def allowed292 : List Nat := [0x8000000000000000000,0x40000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 292. -/
noncomputable def tree292 : ParitySearchTree := (.split 19 (.pack [2]) (.split 22 (.pack [3]) (.split 35 (.pack [7]) (.split 37 (.pack [8]) (.split 38 (.pack [9]) (.split 47 (.pack [10]) (.split 49 (.pack [11]) (.split 60 (.pack [1]) (.split 62 (.pack [1]) (.split 63 (.pack [12]) (.split 75 .done (.split 102 .done (.split 123 (.pack [7]) (.split 125 (.pack [0]) (.split 139 (.pack [3]) (.split 140 (.pack [4]) (.split 150 (.pack [5]) (.split 179 (.pack [13]) (.zero 6)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 292. -/
theorem checked292 : checkParitySearch 8 (fun q => (rows292 >>> (256*q)) &&& (2^256-1)) 0x40 (allowed292.contains) tree292 0xfff17ff7fffffffdbfed7e97fdffffffafffbffff9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 293. -/
noncomputable def rows293 : Nat := 0x60000000000000002000000400480000000000000000000000000000000000000000a0000000000000008000001001200000000000000000000000000000008000000c000000000000000000000400480000000000000000000000000000002000001800000000000000000000010012000000000000000000000000000000002000000a0000000000000000000001001200000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000010000001800000000000000000000080090000000000000000000000000000000001000000180000000000000000000008009000000000000000000000000000080100028028040000008009006006800080480000000000000000000000000000004000003000000000000000000000020024000000000000000000000000000000100000050000000000000000000000800900000000000000000000000140000000080000000012005005a0000000000040000000000000000000000000000000000200000030048000000000000000001000000000000000000000000000000000010000005002400000000000000000080

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 293. -/
noncomputable def allowed293 : List Nat := [0x8000000000000000000,0x40000000000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 293. -/
noncomputable def tree293 : ParitySearchTree := (.split 7 (.pack [0]) (.split 10 (.pack [2]) (.split 19 (.pack [3]) (.split 35 (.pack [7]) (.split 37 (.pack [9]) (.split 38 (.pack [8]) (.split 49 (.pack [12]) (.split 50 (.pack [11]) (.split 60 (.pack [10]) (.split 63 (.pack [13]) (.split 75 .done (.split 102 .done (.split 111 (.pack [6]) (.split 113 (.pack [4]) (.split 123 (.pack [7]) (.split 125 (.pack [1]) (.split 140 (.pack [6]) (.split 151 (.pack [10]) (.zero 5)))))))))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 293. -/
theorem checked293 : checkParitySearch 8 (fun q => (rows293 >>> (256*q)) &&& (2^256-1)) 0x20 (allowed293.contains) tree293 0xfff17fbfff7ffffdbfed7e97fdffffffffffbffbf9fff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 294. -/
noncomputable def rows294 : Nat := 0x1c000003803f00000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 294. -/
noncomputable def allowed294 : List Nat := [0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 294. -/
noncomputable def tree294 : ParitySearchTree := (.split 60 (.pack [6]) (.split 61 .done (.split 62 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.zero 10)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 294. -/
theorem checked294 : checkParitySearch 8 (fun q => (rows294 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed294.contains) tree294 0xfff11ffaffcfffffffffffffffffff9ff3ff0ffe7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 295. -/
noncomputable def rows295 : Nat := 0x1c000003803f00000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c00000000000000040000008009000000000000000000000000000000040000014000000000000000000000200240000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 295. -/
noncomputable def allowed295 : List Nat := [0x1000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 295. -/
noncomputable def tree295 : ParitySearchTree := (.split 60 .done (.split 61 (.pack [6]) (.split 62 .done (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [9]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.zero 10)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 295. -/
theorem checked295 : checkParitySearch 8 (fun q => (rows295 >>> (256*q)) &&& (2^256-1)) 0x400 (allowed295.contains) tree295 0xfff11ff77fd7ffffffffffffffffff9ff5ff0ffebffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 296. -/
noncomputable def rows296 : Nat := 0x1c000003803f00000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 296. -/
noncomputable def allowed296 : List Nat := [0x1000000000000000,0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 296. -/
noncomputable def tree296 : ParitySearchTree := (.split 60 .done (.split 61 .done (.split 62 .done (.split 63 (.pack [6]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.zero 9)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 296. -/
theorem checked296 : checkParitySearch 8 (fun q => (rows296 >>> (256*q)) &&& (2^256-1)) 0x200 (allowed296.contains) tree296 0xfff11fe8ffefffffffffffffffffff9ff5ff0fff7ffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 297. -/
noncomputable def rows297 : Nat := 0x1c000003803f00000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000000000a000000000000000800000100120000000000000000000000000000000000000c0000000000000004000000800900000000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000000000000000400000140010000000000000000002002000000000000000000000000000000020000018000800000000000000000100100000000000000000000000000000000008000000c012000000000000000000400000000000000000000000000000000004000001400900000000000000000020000000000000000000000000000000000200000180048000000000000000001

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 297. -/
noncomputable def allowed297 : List Nat := [0x1000000000000000,0x2000000000000000,0x4000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 297. -/
noncomputable def tree297 : ParitySearchTree := (.split 60 .done (.split 61 .done (.split 62 .done (.split 63 (.pack [6]) (.split 64 (.pack [7]) (.split 65 (.pack [8]) (.split 75 (.pack [0]) (.split 76 (.pack [1]) (.split 77 (.pack [2]) (.split 102 (.pack [4]) (.split 103 (.pack [5]) (.split 104 (.pack [3]) (.zero 9)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 297. -/
theorem checked297 : checkParitySearch 8 (fun q => (rows297 >>> (256*q)) &&& (2^256-1)) 0x200 (allowed297.contains) tree297 0xfff11fe57ff7ffffffffffffffffff9ff3ff0fffbffff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 298. -/
noncomputable def rows298 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000000000000000001c000003803f00000000000000000000000000000000000000c0000000000000020000004004800000000000000000000000000000000000000060000000000000010000002002400000000000000000000000000000006000000c00c000000010000002002700060360000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000a00000000c00400100140000012000000000006004c0200000000000000000000000c0000000100000000024003003600000000000800

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 298. -/
noncomputable def allowed298 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 298. -/
noncomputable def tree298 : ParitySearchTree := (.split 60 (.pack [0]) (.split 61 (.pack [0]) (.split 62 (.pack [5]) (.split 63 (.pack [7]) (.split 64 (.pack [8]) (.split 65 (.pack [4]) (.split 75 (.pack [1]) (.split 76 .done (.split 77 (.pack [9]) (.split 102 (.pack [2]) (.split 103 (.pack [2]) (.split 104 (.pack [3]) (.zero 6)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 298. -/
theorem checked298 : checkParitySearch 8 (fun q => (rows298 >>> (256*q)) &&& (2^256-1)) 0x42 (allowed298.contains) tree298 0xfff0ffeffffffff93ffe7f27ffffffffcfff7ffffcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 299. -/
noncomputable def rows299 : Nat := 0x6000000000000001000000200240000000000000000000000000000000000000005000000000000000400000080090000000000000000000000000000000000000600000000000000020000004004800000000000000000000000000000000000000000000000000001c000003803f00000000000000000000000000000000000000c000000000000002000000400480000000000000000000000000000000000000006000000000000001000000200240000000000000000000000000000000400000140000000000000000000002002400000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000000000000c000000010000002002400300360000000000000000000000000000000000000008000000c00200000000000000000040040000000000000000000a00000000c00400100140000012000000000006004c02

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 299. -/
noncomputable def allowed299 : List Nat := [0x10000000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 299. -/
noncomputable def tree299 : ParitySearchTree := (.split 60 (.pack [3]) (.split 61 (.pack [4]) (.split 62 (.pack [6]) (.split 63 (.pack [8]) (.split 64 (.pack [9]) (.split 65 (.pack [5]) (.split 75 (.pack [0]) (.split 76 .done (.split 77 (.pack [10]) (.split 102 (.pack [1]) (.split 103 (.pack [1]) (.split 104 (.pack [2]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 299. -/
theorem checked299 : checkParitySearch 8 (fun q => (rows299 >>> (256*q)) &&& (2^256-1)) 0x81 (allowed299.contains) tree299 0xfff0ff7ffefffff93ffe7f27ffffffffffff7ff7fcfff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 300. -/
noncomputable def rows300 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e00000000000000000000000000000000000001800000000000000400000080090000000000000000000000000000000000000280000000000000020000004004800000000000000000000000000000000000030000000000000001000000200240000000000000000000000000000000020000018000000000000000000000100120000000000000000000000000000000000000000c0000000100000020024003003600000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 300. -/
noncomputable def allowed300 : List Nat := [0x2000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 300. -/
noncomputable def tree300 : ParitySearchTree := (.split 57 (.pack [5]) (.split 58 (.pack [6]) (.split 59 (.pack [7]) (.split 60 (.pack [4]) (.split 61 .done (.split 62 (.pack [3]) (.split 72 (.pack [9]) (.split 73 (.pack [10]) (.split 74 (.pack [11]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 8)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 300. -/
theorem checked300 : checkParitySearch 8 (fun q => (rows300 >>> (256*q)) &&& (2^256-1)) 0x100 (allowed300.contains) tree300 0xfff03ff8feefffbffbffffff7ffffffff3ff7ffebfeff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 301. -/
noncomputable def rows301 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e0000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000008000000c0000000000000000000004004800000000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 301. -/
noncomputable def allowed301 : List Nat := [0x1000000000000000,0x2000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 301. -/
noncomputable def tree301 : ParitySearchTree := (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 60 .done (.split 61 .done (.split 62 (.pack [3]) (.split 72 (.pack [8]) (.split 73 (.pack [9]) (.split 74 (.pack [10]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 301. -/
theorem checked301 : checkParitySearch 8 (fun q => (rows301 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed301.contains) tree301 0xfff03fee7ec7ffbffbffffff7ffffffff9ff7fffffeff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 302. -/
noncomputable def rows302 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e0000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000000c0000000100000020024003003600000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 302. -/
noncomputable def allowed302 : List Nat := [0x1000000000000000,0x2000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 302. -/
noncomputable def tree302 : ParitySearchTree := (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 60 .done (.split 61 .done (.split 62 (.pack [3]) (.split 72 (.pack [8]) (.split 73 (.pack [9]) (.split 74 (.pack [10]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 302. -/
theorem checked302 : checkParitySearch 8 (fun q => (rows302 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed302.contains) tree302 0xfff03feafecfffbffbffffff7ffffffff5ff7fffbfeff 0 1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Packed parity neighborhoods for affine fiber 303. -/
noncomputable def rows303 : Nat := 0xc0000000000000020000004004800000000000000000000000000000000000014000000000000001000000200240000000000000000000000000000000000001800000000000000080000010012000000000000000000000000000000000000000000000000000000038000007007e0000000000000000000000000000000000000180000000000000040000008009000000000000000000000000000000000000028000000000000002000000400480000000000000000000000000000000000003000000000000000100000020024000000000000000000000000000000000000000000c0000000100000020024003003600000000000000000000000000000000000000010000001802400000000000000000080000000000000000000000000000000000800000280120000000000000000004000000000000000000000000000000000040000030009000000000000000000200

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Candidate outside supports for affine fiber 303. -/
noncomputable def allowed303 : List Nat := [0x1000000000000000,0x2000000000000000]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Exhaustive parity-search certificate for affine fiber 303. -/
noncomputable def tree303 : ParitySearchTree := (.split 57 (.pack [4]) (.split 58 (.pack [5]) (.split 59 (.pack [6]) (.split 60 .done (.split 61 .done (.split 62 (.pack [3]) (.split 72 (.pack [8]) (.split 73 (.pack [9]) (.split 74 (.pack [10]) (.split 99 (.pack [1]) (.split 100 (.pack [2]) (.split 101 (.pack [0]) (.zero 7)))))))))))))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The kernel verifies every branch of affine fiber 303. -/
theorem checked303 : checkParitySearch 8 (fun q => (rows303 >>> (256*q)) &&& (2^256-1)) 0x80 (allowed303.contains) tree303 0xfff03fe77ed7ffbffbffffff7ffffffff3ff7fff7feff 0 1 = true := by decide +kernel

end Quantum.Stabilizer.Homological.F2Mask.AffineSearchData

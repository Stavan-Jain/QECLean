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

import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DeepCensusData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineExceptions
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Join
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopBank

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.DeepBank
open F2Mask
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Verify the bank index attached to each explicitly listed normalized sheet. -/
noncomputable def check (beta : Nat) (entries : List (Nat × Nat)) : Bool :=
  entries.all (fun p => decide (p.2 < 58130 ∧ bottomJoin p.1 beta = topBankMask p.2))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A checked lookup table puts every listed sheet into the common top bank. -/
theorem mem_bank {beta a : Nat} {entries : List (Nat × Nat)}
    (hc : check beta entries = true) (ha : a ∈ entries.map Prod.fst) :
    ∃ j : Fin 58130, bottomJoin a beta = topBankMask j := by
  obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
  have h := of_decide_eq_true ((List.all_eq_true.mp hc) p hp)
  exact ⟨⟨p.2, h.1⟩, hpa ▸ h.2⟩

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Bank indices of the normalized cap-five lifts in exceptional fiber 0. -/
noncomputable def entries0 : List (Nat × Nat) := [(0xe00000249201049,56325),(0xe00009201040240,56326),(0xe00048008008001,56327),(0x400d00081200204200,56328),(0x800c80101200202200,56329),(0x8000000001249041009,56303),(0x8000000008201200200,2331),(0x8000000040040009248,56304),(0x8000000049008248041,56305),(0x8002001800400000068,56308),(0x8004001400800000058,56309),(0x8008000e00200200040,10065),(0x30000001001200200000,2333),(0x38000e01000200040040,56332),(0x48007000000200000000,10066),(0x1008080000100020004849,56297),(0x1008100000080010002449,56298),(0x1008180007000000000049,56299),(0x2001000c80108020000000,56291),(0x2009800000001021002000,56290),(0x2010140604000000000049,56293),(0x2018140804001000240009,56292),(0x3001400c00000211204049,56174),(0x3009000100089210200049,56147),(0x30200c0802000200040040,56187),(0x30280c0602001200200000,56186),(0xa000400c00000221204048,57083),(0xa008000100089220200048,57081),(0xb000000c80108010000001,57077),(0xb008800000001011002001,57075)]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The indexed sheet table is exactly the certified affine census. -/
theorem entries0_sheets : entries0.map Prod.fst = DeepCensusData.lifts0 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each normalized exceptional lift belongs to the common top bank. -/
theorem checked0 : check 0x7008000c00001200200049 entries0 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of exceptional deep fiber 0 reaches the top bank up to deck action. -/
theorem complete0 {a : Nat} (ha : a < 2^90)
    (he : reconX FiberData.bottomEColumns a = reconX FiberData.bottomRColumns 0x7008000c00001200200049)
    (hw : bitCount 90 (outsideMask a 0x7008000c00001200200049) ≤ 5) :
    ∃ j : Fin 58130, bottomJoin a 0x7008000c00001200200049 = topBankMask j ∨
      bottomJoin (a ^^^ 0x7008000c00001200200049) 0x7008000c00001200200049 = topBankMask j := by
  rcases AffineExceptions.deepComplete0 ha he hw with h | h
  · obtain ⟨j, hj⟩ := mem_bank checked0 (entries0_sheets.symm ▸ h)
    exact ⟨j, Or.inl hj⟩
  · obtain ⟨j, hj⟩ := mem_bank checked0 (entries0_sheets.symm ▸ h)
    exact ⟨j, Or.inr hj⟩

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Bank indices of the normalized cap-five lifts in exceptional fiber 1. -/
noncomputable def entries1 : List (Nat × Nat) := [(0x240000040000000,101),(0x2701b0070006000,54413),(0x1040200040040006,54418),(0x180240180070006c00,54481),(0x20018000020004e008,54352),(0x2002481b003000f001,54353),(0x200278000000009001,54354),(0x240200000048000c00,54386),(0x3c0200180078006000,54397),(0x6002800c0040003000,54485),(0xa00300140040005000,54531),(0xc003c0180040006000,54548),(0xe00000180200048008,54547),(0x10000481b0070009001,54586),(0x100007800004000f001,54587),(0x1040000000008006c00,54601),(0x11c0000180038000000,54602),(0x1200040000000006000,102),(0x12000701b0030000000,54557),(0x1380040180030000c00,54583),(0x14000800c0000005000,54620),(0x1800100140000003000,54636),(0x1e001c0180000000000,54637),(0x220064000000001e003,54641),(0x3000440000040018003,54799),(0x4200a4000000002e005,54804),(0x5000840000040028005,54871),(0x80000003801c0008008,54959),(0x8201040000200036000,54950),(0x2000002001c003600e001,55686),(0x2012000001c0076008001,55748),(0xc00000240180076006000,55927),(0xc01200040180036000000,55929),(0xe00000200040000008001,55931),(0xe0120000004004000e001,55933),(0x20002002c014002800e001,56079),(0x200040020018002800d001,56082),(0x20010000c0140068008001,56084),(0x200160000018006800b001,56085),(0x40002003400c001800e001,56282),(0x400080020018001800b001,56286),(0x40010001400c0058008001,56288),(0x4001a0000018005800d001,56289),(0x60000003c0180070000000,56321),(0x600020000018023004e008,56302),(0x6000c00240000070006000,56322),(0x60012001c0180030006000,56323),(0x6001e00040000030000000,56324),(0x8000000000180040008000,103),(0x800000003003007000e000,56963),(0x800018000000007000ec00,56967),(0x8000200008030030007001,56959),(0x8000200038180000001001,56960),(0x8000240040180048008c00,56961),(0x80003c004000007800e000,56962),(0x80006000c014004000b000,56968),(0x8000a001400c004000d000,56969),(0x8000c0018000004000e000,56970),(0x800120020018000000e000,2364),(0x8002200400180000016003,57012),(0x8004200800180000026005,57014),(0x8200000040040036006001,57056),(0x8c0000000000007600e000,57070),(0x8e000000401c0000000001,57071),(0xa0002000800c0028006001,57073),(0xa000400040000028005001,57074),(0xc000200100140018006001,57080),(0xc000800040000018003001,57082),(0xe000000180000070008000,57084),(0xe000c0000018007000e000,57085),(0x10000000600180080008003,57418),(0x100012004001800c000e003,57421),(0x100022002001800c0016000,57422),(0x10003000000180080010000,57425),(0x18000000440000080000003,57510),(0x180022000400000c001e000,57511),(0x20000000a00180100008005,57927),(0x2000120080018014000e005,57928),(0x20004200200180140026000,57929),(0x20005000000180100020000,57931),(0x28000000840000100000005,58016),(0x2800420004000014002e000,58017)]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The indexed sheet table is exactly the certified affine census. -/
theorem entries1_sheets : entries1.map Prod.fst = DeepCensusData.lifts1 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each normalized exceptional lift belongs to the common top bank. -/
theorem checked1 : check 0x100020004018007000e001 entries1 = true := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every light solution of exceptional deep fiber 1 reaches the top bank up to deck action. -/
theorem complete1 {a : Nat} (ha : a < 2^90)
    (he : reconX FiberData.bottomEColumns a = reconX FiberData.bottomRColumns 0x100020004018007000e001)
    (hw : bitCount 90 (outsideMask a 0x100020004018007000e001) ≤ 5) :
    ∃ j : Fin 58130, bottomJoin a 0x100020004018007000e001 = topBankMask j ∨
      bottomJoin (a ^^^ 0x100020004018007000e001) 0x100020004018007000e001 = topBankMask j := by
  rcases AffineExceptions.deepComplete1 ha he hw with h | h
  · obtain ⟨j, hj⟩ := mem_bank checked1 (entries1_sheets.symm ▸ h)
    exact ⟨j, Or.inl hj⟩
  · obtain ⟨j, hj⟩ := mem_bank checked1 (entries1_sheets.symm ▸ h)
    exact ⟨j, Or.inr hj⟩

#print axioms complete0
#print axioms complete1
end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepBank

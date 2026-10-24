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

import QEC.Stabilizer.Framework.Homological.Certificate.PackedDigits

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFiberData
/-- The exact certificate shadows: twenty-six flat fibers, followed by two cap-five fibers. -/
noncomputable def betaPacked : Nat := 0x40008001006001c00380047008000c000012002000490048008d80181000000000c0480084800810000b000030090011200202000340000c0900104800820000700003240040048008000c010001d0010004800c001401000132002001200280060040002c0080004802c00a001000830010001200680300040010c0000244840800008100c030000121220200004040280c00009049008000201006030000013202200000440060c00000948108000021001430000049208200001040030c00200041000c00c012002300000036006000000c000cc000001680280000050002bfc01c00000000000000001c00900148008020000400030012003200200400020000e00200048000000c01000230040001201000180040040c000002080480000090001b0000000d80180000030000c0000004800800000100003

/-- Read one deep shadow in its original affine-certificate coordinate frame. -/
noncomputable def betaAt (i : Nat) : Nat := PackedDigits.lane 90 i betaPacked

end Quantum.Stabilizer.Homological.BB.Bravyi360.DeepFiberData

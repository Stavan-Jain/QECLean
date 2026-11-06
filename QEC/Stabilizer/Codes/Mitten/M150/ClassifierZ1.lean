/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z1Part0
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z1Part1
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z1Part2
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z1Part3
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z1Part4
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z1Part5

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for checkAll_Z1. -/
theorem checkAll_Z1 : checkAll m4TZ1 splitsZ1 = true := by
  simp only [checkAll, splitsZ1, List.all_cons, List.all_nil,
    Z1Split0_check, Z1Split1_check, Z1Split2_check, Z1Split3_check,
    Z1Split4_check, Z1Split5_check, Z1Split6_check, Z1Split7_check,
    Z1Split8_check, Z1Split9_check, Z1Split10_check, Z1Split11_check,
    Z1Split12_check, Z1Split13_check, Z1Split14_check, Z1Split15_check,
    Z1Split16_check, Z1Split17_check, Z1Split18_check, Z1Split19_check,
    Z1Split20_check, Z1Split21_check, Z1Split22_check, Z1Split23_check,
    Z1Split24_check, Z1Split25_check, Z1Split26_check, Z1Split27_check,
    Z1Split28_check, Z1Split29_check, Z1Split30_check, Z1Split31_check,
    Z1Split32_check, Z1Split33_check, Z1Split34_check, Z1Split35_check,
    Z1Split36_check, Z1Split37_check, Z1Split38_check, Z1Split39_check,
    Z1Split40_check, Z1Split41_check, Z1Split42_check, Z1Split43_check,
    Z1Split44_check, Z1Split45_check, Z1Split46_check, Z1Split47_check,
    Z1Split48_check, Z1Split49_check, Z1Split50_check, Z1Split51_check,
    Z1Split52_check, Z1Split53_check, Z1Split54_check, Z1Split55_check,
    Z1Split56_check, Z1Split57_check, Z1Split58_check, Z1Split59_check,
    Z1Split60_check, Z1Split61_check, Z1Split62_check, Z1Split63_check,
    Z1Split64_check, Z1Split65_check, Z1Split66_check, Z1Split67_check,
    Z1Split68_check, Z1Split69_check, Z1Split70_check, Z1Split71_check,
    Z1Split72_check, Z1Split73_check, Z1Split74_check, Z1Split75_check,
    Z1Split76_check, Z1Split77_check, Z1Split78_check, Z1Split79_check,
    Z1Split80_check, Z1Split81_check, Z1Split82_check, Z1Split83_check,
    Z1Split84_check, Z1Split85_check, Z1Split86_check, Z1Split87_check,
    Z1Split88_check, Z1Split89_check, Z1Split90_check, Z1Split91_check,
    Z1Split92_check, Z1Split93_check, Z1Split94_check, Bool.and_true]

#print axioms checkAll_Z1

end Quantum.Stabilizer.Homological.LP.M150

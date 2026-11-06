/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z0Part0
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z0Part1
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z0Part2
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z0Part3
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z0Part4
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.Z0Part5

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for checkAll_Z0. -/
theorem checkAll_Z0 : checkAll m4TZ0 splitsZ0 = true := by
  simp only [checkAll, splitsZ0, List.all_cons, List.all_nil,
    Z0Split0_check, Z0Split1_check, Z0Split2_check, Z0Split3_check,
    Z0Split4_check, Z0Split5_check, Z0Split6_check, Z0Split7_check,
    Z0Split8_check, Z0Split9_check, Z0Split10_check, Z0Split11_check,
    Z0Split12_check, Z0Split13_check, Z0Split14_check, Z0Split15_check,
    Z0Split16_check, Z0Split17_check, Z0Split18_check, Z0Split19_check,
    Z0Split20_check, Z0Split21_check, Z0Split22_check, Z0Split23_check,
    Z0Split24_check, Z0Split25_check, Z0Split26_check, Z0Split27_check,
    Z0Split28_check, Z0Split29_check, Z0Split30_check, Z0Split31_check,
    Z0Split32_check, Z0Split33_check, Z0Split34_check, Z0Split35_check,
    Z0Split36_check, Z0Split37_check, Z0Split38_check, Z0Split39_check,
    Z0Split40_check, Z0Split41_check, Z0Split42_check, Z0Split43_check,
    Z0Split44_check, Z0Split45_check, Z0Split46_check, Z0Split47_check,
    Z0Split48_check, Z0Split49_check, Z0Split50_check, Z0Split51_check,
    Z0Split52_check, Z0Split53_check, Z0Split54_check, Z0Split55_check,
    Z0Split56_check, Z0Split57_check, Z0Split58_check, Z0Split59_check,
    Z0Split60_check, Z0Split61_check, Z0Split62_check, Z0Split63_check,
    Z0Split64_check, Z0Split65_check, Z0Split66_check, Z0Split67_check,
    Z0Split68_check, Z0Split69_check, Z0Split70_check, Z0Split71_check,
    Z0Split72_check, Z0Split73_check, Z0Split74_check, Z0Split75_check,
    Z0Split76_check, Z0Split77_check, Z0Split78_check, Z0Split79_check,
    Z0Split80_check, Z0Split81_check, Z0Split82_check, Z0Split83_check,
    Z0Split84_check, Z0Split85_check, Z0Split86_check, Z0Split87_check,
    Z0Split88_check, Z0Split89_check, Z0Split90_check, Z0Split91_check,
    Z0Split92_check, Z0Split93_check, Z0Split94_check, Bool.and_true]

#print axioms checkAll_Z0

end Quantum.Stabilizer.Homological.LP.M150

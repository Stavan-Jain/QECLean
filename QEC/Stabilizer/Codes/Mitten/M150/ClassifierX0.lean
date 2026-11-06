/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X0Part0
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X0Part1
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X0Part2
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X0Part3
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X0Part4
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X0Part5

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for checkAll_X0. -/
theorem checkAll_X0 : checkAll m4TX0 splitsX0 = true := by
  simp only [checkAll, splitsX0, List.all_cons, List.all_nil,
    X0Split0_check, X0Split1_check, X0Split2_check, X0Split3_check,
    X0Split4_check, X0Split5_check, X0Split6_check, X0Split7_check,
    X0Split8_check, X0Split9_check, X0Split10_check, X0Split11_check,
    X0Split12_check, X0Split13_check, X0Split14_check, X0Split15_check,
    X0Split16_check, X0Split17_check, X0Split18_check, X0Split19_check,
    X0Split20_check, X0Split21_check, X0Split22_check, X0Split23_check,
    X0Split24_check, X0Split25_check, X0Split26_check, X0Split27_check,
    X0Split28_check, X0Split29_check, X0Split30_check, X0Split31_check,
    X0Split32_check, X0Split33_check, X0Split34_check, X0Split35_check,
    X0Split36_check, X0Split37_check, X0Split38_check, X0Split39_check,
    X0Split40_check, X0Split41_check, X0Split42_check, X0Split43_check,
    X0Split44_check, X0Split45_check, X0Split46_check, X0Split47_check,
    X0Split48_check, X0Split49_check, X0Split50_check, X0Split51_check,
    X0Split52_check, X0Split53_check, X0Split54_check, X0Split55_check,
    X0Split56_check, X0Split57_check, X0Split58_check, X0Split59_check,
    X0Split60_check, X0Split61_check, X0Split62_check, X0Split63_check,
    X0Split64_check, X0Split65_check, X0Split66_check, X0Split67_check,
    X0Split68_check, X0Split69_check, X0Split70_check, X0Split71_check,
    X0Split72_check, X0Split73_check, X0Split74_check, X0Split75_check,
    X0Split76_check, X0Split77_check, X0Split78_check, X0Split79_check,
    X0Split80_check, X0Split81_check, X0Split82_check, X0Split83_check,
    X0Split84_check, X0Split85_check, X0Split86_check, X0Split87_check,
    X0Split88_check, X0Split89_check, X0Split90_check, X0Split91_check,
    X0Split92_check, X0Split93_check, X0Split94_check, Bool.and_true]

#print axioms checkAll_X0

end Quantum.Stabilizer.Homological.LP.M150

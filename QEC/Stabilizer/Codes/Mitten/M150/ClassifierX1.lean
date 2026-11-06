/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X1Part0
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X1Part1
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X1Part2
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X1Part3
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X1Part4
import QEC.Stabilizer.Codes.Mitten.M150.ClassifierParts.X1Part5

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for checkAll_X1. -/
theorem checkAll_X1 : checkAll m4TX1 splitsX1 = true := by
  simp only [checkAll, splitsX1, List.all_cons, List.all_nil,
    X1Split0_check, X1Split1_check, X1Split2_check, X1Split3_check,
    X1Split4_check, X1Split5_check, X1Split6_check, X1Split7_check,
    X1Split8_check, X1Split9_check, X1Split10_check, X1Split11_check,
    X1Split12_check, X1Split13_check, X1Split14_check, X1Split15_check,
    X1Split16_check, X1Split17_check, X1Split18_check, X1Split19_check,
    X1Split20_check, X1Split21_check, X1Split22_check, X1Split23_check,
    X1Split24_check, X1Split25_check, X1Split26_check, X1Split27_check,
    X1Split28_check, X1Split29_check, X1Split30_check, X1Split31_check,
    X1Split32_check, X1Split33_check, X1Split34_check, X1Split35_check,
    X1Split36_check, X1Split37_check, X1Split38_check, X1Split39_check,
    X1Split40_check, X1Split41_check, X1Split42_check, X1Split43_check,
    X1Split44_check, X1Split45_check, X1Split46_check, X1Split47_check,
    X1Split48_check, X1Split49_check, X1Split50_check, X1Split51_check,
    X1Split52_check, X1Split53_check, X1Split54_check, X1Split55_check,
    X1Split56_check, X1Split57_check, X1Split58_check, X1Split59_check,
    X1Split60_check, X1Split61_check, X1Split62_check, X1Split63_check,
    X1Split64_check, X1Split65_check, X1Split66_check, X1Split67_check,
    X1Split68_check, X1Split69_check, X1Split70_check, X1Split71_check,
    X1Split72_check, X1Split73_check, X1Split74_check, X1Split75_check,
    X1Split76_check, X1Split77_check, X1Split78_check, X1Split79_check,
    X1Split80_check, X1Split81_check, X1Split82_check, X1Split83_check,
    X1Split84_check, X1Split85_check, X1Split86_check, X1Split87_check,
    X1Split88_check, X1Split89_check, X1Split90_check, X1Split91_check,
    X1Split92_check, X1Split93_check, X1Split94_check, Bool.and_true]

#print axioms checkAll_X1

end Quantum.Stabilizer.Homological.LP.M150

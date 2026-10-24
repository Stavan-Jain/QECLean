/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_trellis_bridges.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Framework.Homological.Certificate.MaskPermutation
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TrellisBasisBridge

noncomputable section

set_option maxRecDepth 100000

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The trellis ordering as an equivalence of the ninety coordinate positions. -/
noncomputable def stabCoordinateEquiv : Fin 90 ≃ Fin 90 where
  toFun i := Fin.ofNat 90 (([47, 37, 38, 9, 3, 11, 24, 33, 35, 66, 76, 78, 59, 86, 58, 44, 52, 43, 12, 6, 8, 28, 17, 16, 72, 74, 64, 87, 57, 70, 42, 39, 46, 29, 20, 22, 27, 18, 5, 89, 56, 83, 69, 61, 77, 25, 34, 32, 21, 19, 7, 63, 88, 62, 81, 79, 71, 36, 49, 45, 26, 0, 1, 31, 2, 13, 75, 55, 68, 80, 60, 73, 51, 40, 53, 30, 4, 10, 23, 15, 14, 65, 54, 84, 67, 82, 85, 48, 50, 41] : List Nat)[i.val]!)
  invFun i := Fin.ofNat 90 (([61, 62, 64, 4, 76, 38, 19, 50, 20, 3, 77, 5, 18, 65, 80, 79, 23, 22, 37, 49, 34, 48, 35, 78, 6, 45, 60, 36, 21, 33, 75, 63, 47, 7, 46, 8, 57, 1, 2, 31, 73, 89, 30, 17, 15, 59, 32, 0, 87, 58, 88, 72, 16, 74, 82, 67, 40, 28, 14, 12, 70, 43, 53, 51, 26, 81, 9, 84, 68, 42, 29, 56, 24, 71, 25, 66, 10, 44, 11, 55, 69, 54, 85, 41, 83, 86, 13, 27, 52, 39] : List Nat)[i.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each coordinate column agrees with the trellis coordinate permutation. -/
theorem stab_permutation_columns : ∀ i : Fin 90,
    reconX stabPermutation (2 ^ i.val) = 2 ^ (stabCoordinateEquiv i).val := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Trellis reindexing preserves Hamming weight for every laboratory mask. -/
theorem stab_permutation_weight {word : Nat} (hword : word < 2 ^ 90) :
    bitCount 90 (reconX stabPermutation word) = bitCount 90 word :=
  reconX_permutation_weight stabCoordinateEquiv stabPermutation stab_permutation_columns hword

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Trellis reindexing never identifies distinct bounded laboratory masks. -/
theorem stab_permutation_injective {a b : Nat} (ha : a < 2 ^ 90) (hb : b < 2 ^ 90)
    (heq : reconX stabPermutation a = reconX stabPermutation b) : a = b :=
  reconX_permutation_injective stabCoordinateEquiv stabPermutation
    stab_permutation_columns ha hb heq

#print axioms stab_permutation_weight

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The trellis ordering as an equivalence of the ninety coordinate positions. -/
noncomputable def cycleCoordinateEquiv : Fin 90 ≃ Fin 90 where
  toFun i := Fin.ofNat 90 (([25, 32, 34, 48, 41, 50, 67, 85, 82, 65, 84, 54, 23, 14, 15, 30, 10, 4, 51, 53, 40, 80, 73, 60, 75, 68, 55, 31, 13, 2, 26, 1, 0, 36, 45, 49, 81, 71, 79, 63, 62, 88, 21, 7, 19, 47, 38, 37, 69, 77, 61, 89, 83, 56, 27, 5, 18, 29, 22, 20, 42, 46, 39, 87, 70, 57, 72, 64, 74, 28, 16, 17, 12, 8, 6, 44, 43, 52, 59, 58, 86, 66, 78, 76, 24, 35, 33, 9, 11, 3] : List Nat)[i.val]!)
  invFun i := Fin.ofNat 90 (([32, 31, 29, 89, 17, 55, 74, 43, 73, 87, 16, 88, 72, 28, 13, 14, 70, 71, 56, 44, 59, 42, 58, 12, 84, 0, 30, 54, 69, 57, 15, 27, 1, 86, 2, 85, 33, 47, 46, 62, 20, 4, 60, 76, 75, 34, 61, 45, 3, 35, 5, 18, 77, 19, 11, 26, 53, 65, 79, 78, 23, 50, 40, 39, 67, 9, 81, 6, 25, 48, 64, 37, 66, 22, 68, 24, 83, 49, 82, 38, 21, 36, 8, 52, 10, 7, 80, 63, 41, 51] : List Nat)[i.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each coordinate column agrees with the trellis coordinate permutation. -/
theorem cycle_permutation_columns : ∀ i : Fin 90,
    reconX cyclePermutation (2 ^ i.val) = 2 ^ (cycleCoordinateEquiv i).val := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Trellis reindexing preserves Hamming weight for every laboratory mask. -/
theorem cycle_permutation_weight {word : Nat} (hword : word < 2 ^ 90) :
    bitCount 90 (reconX cyclePermutation word) = bitCount 90 word :=
  reconX_permutation_weight cycleCoordinateEquiv cyclePermutation cycle_permutation_columns hword

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Trellis reindexing never identifies distinct bounded laboratory masks. -/
theorem cycle_permutation_injective {a b : Nat} (ha : a < 2 ^ 90) (hb : b < 2 ^ 90)
    (heq : reconX cyclePermutation a = reconX cyclePermutation b) : a = b :=
  reconX_permutation_injective cycleCoordinateEquiv cyclePermutation
    cycle_permutation_columns ha hb heq

#print axioms cycle_permutation_weight

end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

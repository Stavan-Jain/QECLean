/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/bravyi360_kernel/generate.py
Emitter, relative to generator directory:
  emitters/generate_trellis_censuses.py
Data and SHA-256 hashes: audit_manifest.json
Regenerate:
  QECLEAN_ROOT=/path/to/QECLean \
    python3 experiments/bb_lab/scripts/bravyi360_kernel/generate.py --force
-/

import QEC.Stabilizer.Framework.Homological.Certificate.FastTrellis

noncomputable section

set_option maxRecDepth 1000000

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Terminal stage of the certified encoder. -/
private noncomputable def stabRaw90 (_offset degree : Nat) : PackedProgram 42 degree 0 0 := PackedProgram.done 0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Terminal metadata suffix. -/
private noncomputable def stabSteps90 (_offset : Nat) : List PackedStep := []

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The terminal stage leaves its table unchanged. -/
private theorem stab_numeric90 (offset degree : Nat) : (stabRaw90 offset degree).numeric = (fun table => (stabSteps90 offset).foldl (packedStep 42 degree) table) := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 89. -/
private noncomputable def stabRaw89 (offset degree : Nat) : PackedProgram 42 degree 1 0 := PackedProgram.emit [0] (offset.testBit 89 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (stabRaw90 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps89 (offset : Nat) : List PackedStep := (1, false, [0], 0, (offset.testBit 89 ^^ true)) :: stabSteps90 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric89 (offset degree : Nat) :
    (stabRaw89 offset degree).numeric =
      (fun table => (stabSteps89 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw90 offset degree).numeric (packedStep 42 degree table (1, false, [0], 0, (offset.testBit 89 ^^ true))) = _
  rw [stab_numeric90]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 88. -/
private noncomputable def stabRaw88 (offset degree : Nat) : PackedProgram 42 degree 2 0 := PackedProgram.emit [0, 1] (offset.testBit 88 ^^ false) (by decide) (PackedProgram.forgetBitFast 0 (stabRaw89 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps88 (offset : Nat) : List PackedStep := (2, false, [0, 1], 0, (offset.testBit 88 ^^ false)) :: stabSteps89 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric88 (offset degree : Nat) :
    (stabRaw88 offset degree).numeric =
      (fun table => (stabSteps88 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw89 offset degree).numeric (packedStep 42 degree table (2, false, [0, 1], 0, (offset.testBit 88 ^^ false))) = _
  rw [stab_numeric89]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 87. -/
private noncomputable def stabRaw87 (offset degree : Nat) : PackedProgram 42 degree 3 0 := PackedProgram.emit [1] (offset.testBit 87 ^^ true) (by decide) (PackedProgram.forgetBitFast 1 (stabRaw88 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps87 (offset : Nat) : List PackedStep := (3, false, [1], 1, (offset.testBit 87 ^^ true)) :: stabSteps88 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric87 (offset degree : Nat) :
    (stabRaw87 offset degree).numeric =
      (fun table => (stabSteps87 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw88 offset degree).numeric (packedStep 42 degree table (3, false, [1], 1, (offset.testBit 87 ^^ true))) = _
  rw [stab_numeric88]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 86. -/
private noncomputable def stabRaw86 (offset degree : Nat) : PackedProgram 42 degree 4 0 := PackedProgram.emit [0, 1, 2] (offset.testBit 86 ^^ true) (by decide) (PackedProgram.forgetBitFast 1 (stabRaw87 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps86 (offset : Nat) : List PackedStep := (4, false, [0, 1, 2], 1, (offset.testBit 86 ^^ true)) :: stabSteps87 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric86 (offset degree : Nat) :
    (stabRaw86 offset degree).numeric =
      (fun table => (stabSteps86 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw87 offset degree).numeric (packedStep 42 degree table (4, false, [0, 1, 2], 1, (offset.testBit 86 ^^ true))) = _
  rw [stab_numeric87]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 85. -/
private noncomputable def stabRaw85 (offset degree : Nat) : PackedProgram 42 degree 5 0 := PackedProgram.emit [0, 3] (offset.testBit 85 ^^ false) (by decide) (PackedProgram.forgetBitFast 3 (stabRaw86 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps85 (offset : Nat) : List PackedStep := (5, false, [0, 3], 3, (offset.testBit 85 ^^ false)) :: stabSteps86 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric85 (offset degree : Nat) :
    (stabRaw85 offset degree).numeric =
      (fun table => (stabSteps85 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw86 offset degree).numeric (packedStep 42 degree table (5, false, [0, 3], 3, (offset.testBit 85 ^^ false))) = _
  rw [stab_numeric86]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 84. -/
private noncomputable def stabRaw84 (offset degree : Nat) : PackedProgram 42 degree 6 0 := PackedProgram.emit [2, 3] (offset.testBit 84 ^^ false) (by decide) (PackedProgram.forgetBitFast 2 (stabRaw85 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps84 (offset : Nat) : List PackedStep := (6, false, [2, 3], 2, (offset.testBit 84 ^^ false)) :: stabSteps85 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric84 (offset degree : Nat) :
    (stabRaw84 offset degree).numeric =
      (fun table => (stabSteps84 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw85 offset degree).numeric (packedStep 42 degree table (6, false, [2, 3], 2, (offset.testBit 84 ^^ false))) = _
  rw [stab_numeric85]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 83. -/
private noncomputable def stabRaw83 (offset degree : Nat) : PackedProgram 42 degree 7 0 := PackedProgram.emit [1, 5] (offset.testBit 83 ^^ false) (by decide) (PackedProgram.forgetBitFast 1 (stabRaw84 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps83 (offset : Nat) : List PackedStep := (7, false, [1, 5], 1, (offset.testBit 83 ^^ false)) :: stabSteps84 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric83 (offset degree : Nat) :
    (stabRaw83 offset degree).numeric =
      (fun table => (stabSteps83 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw84 offset degree).numeric (packedStep 42 degree table (7, false, [1, 5], 1, (offset.testBit 83 ^^ false))) = _
  rw [stab_numeric84]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 82. -/
private noncomputable def stabRaw82 (offset degree : Nat) : PackedProgram 42 degree 8 0 := PackedProgram.emit [0, 3, 5] (offset.testBit 82 ^^ true) (by decide) (PackedProgram.forgetBitFast 3 (stabRaw83 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps82 (offset : Nat) : List PackedStep := (8, false, [0, 3, 5], 3, (offset.testBit 82 ^^ true)) :: stabSteps83 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric82 (offset degree : Nat) :
    (stabRaw82 offset degree).numeric =
      (fun table => (stabSteps82 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw83 offset degree).numeric (packedStep 42 degree table (8, false, [0, 3, 5], 3, (offset.testBit 82 ^^ true))) = _
  rw [stab_numeric83]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 81. -/
private noncomputable def stabRaw81 (offset degree : Nat) : PackedProgram 42 degree 9 0 := PackedProgram.emit [0, 1, 2, 4, 8] (offset.testBit 81 ^^ true) (by decide) (PackedProgram.forgetBitFast 4 (stabRaw82 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps81 (offset : Nat) : List PackedStep := (9, false, [0, 1, 2, 4, 8], 4, (offset.testBit 81 ^^ true)) :: stabSteps82 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric81 (offset degree : Nat) :
    (stabRaw81 offset degree).numeric =
      (fun table => (stabSteps81 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw82 offset degree).numeric (packedStep 42 degree table (9, false, [0, 1, 2, 4, 8], 4, (offset.testBit 81 ^^ true))) = _
  rw [stab_numeric82]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 80. -/
private noncomputable def stabRaw80 (offset degree : Nat) : PackedProgram 42 degree 10 0 := PackedProgram.emit [2, 3, 4, 6, 8] (offset.testBit 80 ^^ true) (by decide) (PackedProgram.forgetBitFast 6 (stabRaw81 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps80 (offset : Nat) : List PackedStep := (10, false, [2, 3, 4, 6, 8], 6, (offset.testBit 80 ^^ true)) :: stabSteps81 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric80 (offset degree : Nat) :
    (stabRaw80 offset degree).numeric =
      (fun table => (stabSteps80 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw81 offset degree).numeric (packedStep 42 degree table (10, false, [2, 3, 4, 6, 8], 6, (offset.testBit 80 ^^ true))) = _
  rw [stab_numeric81]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 79. -/
private noncomputable def stabRaw79 (offset degree : Nat) : PackedProgram 42 degree 10 0 := PackedProgram.read (width := 10) (PackedProgram.emit [0, 5, 10] (offset.testBit 79 ^^ true) (by decide) (PackedProgram.forgetBitFast 5 (stabRaw80 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps79 (offset : Nat) : List PackedStep := (11, true, [0, 5, 10], 5, (offset.testBit 79 ^^ true)) :: stabSteps80 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric79 (offset degree : Nat) :
    (stabRaw79 offset degree).numeric =
      (fun table => (stabSteps79 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw80 offset degree).numeric (packedStep 42 degree table (11, true, [0, 5, 10], 5, (offset.testBit 79 ^^ true))) = _
  rw [stab_numeric80]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 78. -/
private noncomputable def stabRaw78 (offset degree : Nat) : PackedProgram 42 degree 11 0 := PackedProgram.emit [2, 4, 5, 8] (offset.testBit 78 ^^ false) (by decide) (PackedProgram.forgetBitFast 4 (stabRaw79 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps78 (offset : Nat) : List PackedStep := (11, false, [2, 4, 5, 8], 4, (offset.testBit 78 ^^ false)) :: stabSteps79 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric78 (offset degree : Nat) :
    (stabRaw78 offset degree).numeric =
      (fun table => (stabSteps78 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw79 offset degree).numeric (packedStep 42 degree table (11, false, [2, 4, 5, 8], 4, (offset.testBit 78 ^^ false))) = _
  rw [stab_numeric79]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 77. -/
private noncomputable def stabRaw77 (offset degree : Nat) : PackedProgram 42 degree 11 0 := PackedProgram.emit [2, 4, 7, 10] (offset.testBit 77 ^^ false) (by decide) (stabRaw78 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps77 (offset : Nat) : List PackedStep := (11, false, [2, 4, 7, 10], 11, (offset.testBit 77 ^^ false)) :: stabSteps78 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric77 (offset degree : Nat) :
    (stabRaw77 offset degree).numeric =
      (fun table => (stabSteps77 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw78 offset degree).numeric (packedStep 42 degree table (11, false, [2, 4, 7, 10], 11, (offset.testBit 77 ^^ false))) = _
  rw [stab_numeric78]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 76. -/
private noncomputable def stabRaw76 (offset degree : Nat) : PackedProgram 42 degree 12 0 := PackedProgram.emit [2, 4, 5, 8, 11] (offset.testBit 76 ^^ true) (by decide) (PackedProgram.forgetBitFast 2 (stabRaw77 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps76 (offset : Nat) : List PackedStep := (12, false, [2, 4, 5, 8, 11], 2, (offset.testBit 76 ^^ true)) :: stabSteps77 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric76 (offset degree : Nat) :
    (stabRaw76 offset degree).numeric =
      (fun table => (stabSteps76 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw77 offset degree).numeric (packedStep 42 degree table (12, false, [2, 4, 5, 8, 11], 2, (offset.testBit 76 ^^ true))) = _
  rw [stab_numeric77]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 75. -/
private noncomputable def stabRaw75 (offset degree : Nat) : PackedProgram 42 degree 12 0 := PackedProgram.read (width := 12) (PackedProgram.emit [8, 11, 12] (offset.testBit 75 ^^ true) (by decide) (PackedProgram.forgetBitFast 8 (stabRaw76 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps75 (offset : Nat) : List PackedStep := (13, true, [8, 11, 12], 8, (offset.testBit 75 ^^ true)) :: stabSteps76 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric75 (offset degree : Nat) :
    (stabRaw75 offset degree).numeric =
      (fun table => (stabSteps75 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw76 offset degree).numeric (packedStep 42 degree table (13, true, [8, 11, 12], 8, (offset.testBit 75 ^^ true))) = _
  rw [stab_numeric76]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 74. -/
private noncomputable def stabRaw74 (offset degree : Nat) : PackedProgram 42 degree 13 0 := PackedProgram.emit [3, 6, 7, 11, 12] (offset.testBit 74 ^^ true) (by decide) (PackedProgram.forgetBitFast 7 (stabRaw75 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps74 (offset : Nat) : List PackedStep := (13, false, [3, 6, 7, 11, 12], 7, (offset.testBit 74 ^^ true)) :: stabSteps75 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric74 (offset degree : Nat) :
    (stabRaw74 offset degree).numeric =
      (fun table => (stabSteps74 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw75 offset degree).numeric (packedStep 42 degree table (13, false, [3, 6, 7, 11, 12], 7, (offset.testBit 74 ^^ true))) = _
  rw [stab_numeric75]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 73. -/
private noncomputable def stabRaw73 (offset degree : Nat) : PackedProgram 42 degree 13 0 := PackedProgram.emit [2, 4, 5, 7, 9, 10, 11, 12] (offset.testBit 73 ^^ false) (by decide) (stabRaw74 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps73 (offset : Nat) : List PackedStep := (13, false, [2, 4, 5, 7, 9, 10, 11, 12], 13, (offset.testBit 73 ^^ false)) :: stabSteps74 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric73 (offset degree : Nat) :
    (stabRaw73 offset degree).numeric =
      (fun table => (stabSteps73 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw74 offset degree).numeric (packedStep 42 degree table (13, false, [2, 4, 5, 7, 9, 10, 11, 12], 13, (offset.testBit 73 ^^ false))) = _
  rw [stab_numeric74]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 72. -/
private noncomputable def stabRaw72 (offset degree : Nat) : PackedProgram 42 degree 12 0 := PackedProgram.read (width := 12) (PackedProgram.emit [3, 8, 11, 12] (offset.testBit 72 ^^ false) (by decide) (stabRaw73 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps72 (offset : Nat) : List PackedStep := (13, true, [3, 8, 11, 12], 13, (offset.testBit 72 ^^ false)) :: stabSteps73 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric72 (offset degree : Nat) :
    (stabRaw72 offset degree).numeric =
      (fun table => (stabSteps72 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw73 offset degree).numeric (packedStep 42 degree table (13, true, [3, 8, 11, 12], 13, (offset.testBit 72 ^^ false))) = _
  rw [stab_numeric73]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 71. -/
private noncomputable def stabRaw71 (offset degree : Nat) : PackedProgram 42 degree 13 0 := PackedProgram.emit [0, 2, 4, 5, 8, 11, 12] (offset.testBit 71 ^^ true) (by decide) (PackedProgram.forgetBitFast 8 (stabRaw72 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps71 (offset : Nat) : List PackedStep := (13, false, [0, 2, 4, 5, 8, 11, 12], 8, (offset.testBit 71 ^^ true)) :: stabSteps72 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric71 (offset degree : Nat) :
    (stabRaw71 offset degree).numeric =
      (fun table => (stabSteps71 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw72 offset degree).numeric (packedStep 42 degree table (13, false, [0, 2, 4, 5, 8, 11, 12], 8, (offset.testBit 71 ^^ true))) = _
  rw [stab_numeric72]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 70. -/
private noncomputable def stabRaw70 (offset degree : Nat) : PackedProgram 42 degree 14 0 := PackedProgram.emit [2, 4, 5, 12] (offset.testBit 70 ^^ false) (by decide) (PackedProgram.forgetBitFast 12 (stabRaw71 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps70 (offset : Nat) : List PackedStep := (14, false, [2, 4, 5, 12], 12, (offset.testBit 70 ^^ false)) :: stabSteps71 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric70 (offset degree : Nat) :
    (stabRaw70 offset degree).numeric =
      (fun table => (stabSteps70 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw71 offset degree).numeric (packedStep 42 degree table (14, false, [2, 4, 5, 12], 12, (offset.testBit 70 ^^ false))) = _
  rw [stab_numeric71]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 69. -/
private noncomputable def stabRaw69 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [3, 4, 6, 7, 8, 11, 13, 14] (offset.testBit 69 ^^ false) (by decide) (PackedProgram.forgetBitFast 3 (stabRaw70 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps69 (offset : Nat) : List PackedStep := (15, false, [3, 4, 6, 7, 8, 11, 13, 14], 3, (offset.testBit 69 ^^ false)) :: stabSteps70 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric69 (offset degree : Nat) :
    (stabRaw69 offset degree).numeric =
      (fun table => (stabSteps69 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw70 offset degree).numeric (packedStep 42 degree table (15, false, [3, 4, 6, 7, 8, 11, 13, 14], 3, (offset.testBit 69 ^^ false))) = _
  rw [stab_numeric70]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 68. -/
private noncomputable def stabRaw68 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [2, 3, 4, 5, 6, 13] (offset.testBit 68 ^^ false) (by decide) (PackedProgram.forgetBitFast 6 (stabRaw69 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps68 (offset : Nat) : List PackedStep := (16, false, [2, 3, 4, 5, 6, 13], 6, (offset.testBit 68 ^^ false)) :: stabSteps69 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric68 (offset degree : Nat) :
    (stabRaw68 offset degree).numeric =
      (fun table => (stabSteps68 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw69 offset degree).numeric (packedStep 42 degree table (16, false, [2, 3, 4, 5, 6, 13], 6, (offset.testBit 68 ^^ false))) = _
  rw [stab_numeric69]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 67. -/
private noncomputable def stabRaw67 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [0, 1, 3, 7, 12, 14, 15] (offset.testBit 67 ^^ true) (by decide) (stabRaw68 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps67 (offset : Nat) : List PackedStep := (16, false, [0, 1, 3, 7, 12, 14, 15], 16, (offset.testBit 67 ^^ true)) :: stabSteps68 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric67 (offset degree : Nat) :
    (stabRaw67 offset degree).numeric =
      (fun table => (stabSteps67 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw68 offset degree).numeric (packedStep 42 degree table (16, false, [0, 1, 3, 7, 12, 14, 15], 16, (offset.testBit 67 ^^ true))) = _
  rw [stab_numeric68]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 66. -/
private noncomputable def stabRaw66 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [2, 3, 16] (offset.testBit 66 ^^ true) (by decide) (PackedProgram.forgetBitFast 2 (stabRaw67 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps66 (offset : Nat) : List PackedStep := (17, true, [2, 3, 16], 2, (offset.testBit 66 ^^ true)) :: stabSteps67 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric66 (offset degree : Nat) :
    (stabRaw66 offset degree).numeric =
      (fun table => (stabSteps66 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw67 offset degree).numeric (packedStep 42 degree table (17, true, [2, 3, 16], 2, (offset.testBit 66 ^^ true))) = _
  rw [stab_numeric67]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 65. -/
private noncomputable def stabRaw65 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [2, 7, 14, 15] (offset.testBit 65 ^^ false) (by decide) (stabRaw66 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps65 (offset : Nat) : List PackedStep := (16, false, [2, 7, 14, 15], 16, (offset.testBit 65 ^^ false)) :: stabSteps66 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric65 (offset degree : Nat) :
    (stabRaw65 offset degree).numeric =
      (fun table => (stabSteps65 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw66 offset degree).numeric (packedStep 42 degree table (16, false, [2, 7, 14, 15], 16, (offset.testBit 65 ^^ false))) = _
  rw [stab_numeric66]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 64. -/
private noncomputable def stabRaw64 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [6, 7, 13, 15] (offset.testBit 64 ^^ false) (by decide) (stabRaw65 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps64 (offset : Nat) : List PackedStep := (16, true, [6, 7, 13, 15], 16, (offset.testBit 64 ^^ false)) :: stabSteps65 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric64 (offset degree : Nat) :
    (stabRaw64 offset degree).numeric =
      (fun table => (stabSteps64 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw65 offset degree).numeric (packedStep 42 degree table (16, true, [6, 7, 13, 15], 16, (offset.testBit 64 ^^ false))) = _
  rw [stab_numeric65]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 63. -/
private noncomputable def stabRaw63 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [0, 1, 2, 3, 5, 6] (offset.testBit 63 ^^ false) (by decide) (PackedProgram.forgetBitFast 5 (stabRaw64 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps63 (offset : Nat) : List PackedStep := (16, false, [0, 1, 2, 3, 5, 6], 5, (offset.testBit 63 ^^ false)) :: stabSteps64 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric63 (offset degree : Nat) :
    (stabRaw63 offset degree).numeric =
      (fun table => (stabSteps63 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw64 offset degree).numeric (packedStep 42 degree table (16, false, [0, 1, 2, 3, 5, 6], 5, (offset.testBit 63 ^^ false))) = _
  rw [stab_numeric64]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 62. -/
private noncomputable def stabRaw62 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [0, 3, 5] (offset.testBit 62 ^^ true) (by decide) (stabRaw63 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps62 (offset : Nat) : List PackedStep := (16, false, [0, 3, 5], 16, (offset.testBit 62 ^^ true)) :: stabSteps63 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric62 (offset degree : Nat) :
    (stabRaw62 offset degree).numeric =
      (fun table => (stabSteps62 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw63 offset degree).numeric (packedStep 42 degree table (16, false, [0, 3, 5], 16, (offset.testBit 62 ^^ true))) = _
  rw [stab_numeric63]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 61. -/
private noncomputable def stabRaw61 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [3, 5, 6, 8, 10, 11, 14] (offset.testBit 61 ^^ true) (by decide) (stabRaw62 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps61 (offset : Nat) : List PackedStep := (16, false, [3, 5, 6, 8, 10, 11, 14], 16, (offset.testBit 61 ^^ true)) :: stabSteps62 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric61 (offset degree : Nat) :
    (stabRaw61 offset degree).numeric =
      (fun table => (stabSteps61 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw62 offset degree).numeric (packedStep 42 degree table (16, false, [3, 5, 6, 8, 10, 11, 14], 16, (offset.testBit 61 ^^ true))) = _
  rw [stab_numeric62]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 60. -/
private noncomputable def stabRaw60 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [0, 2, 3, 4, 14, 15] (offset.testBit 60 ^^ false) (by decide) (PackedProgram.forgetBitFast 0 (stabRaw61 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps60 (offset : Nat) : List PackedStep := (17, false, [0, 2, 3, 4, 14, 15], 0, (offset.testBit 60 ^^ false)) :: stabSteps61 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric60 (offset degree : Nat) :
    (stabRaw60 offset degree).numeric =
      (fun table => (stabSteps60 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw61 offset degree).numeric (packedStep 42 degree table (17, false, [0, 2, 3, 4, 14, 15], 0, (offset.testBit 60 ^^ false))) = _
  rw [stab_numeric61]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 59. -/
private noncomputable def stabRaw59 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [0, 1, 2, 3, 5, 6, 7, 9, 10, 13, 16] (offset.testBit 59 ^^ true) (by decide) (stabRaw60 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps59 (offset : Nat) : List PackedStep := (17, false, [0, 1, 2, 3, 5, 6, 7, 9, 10, 13, 16], 17, (offset.testBit 59 ^^ true)) :: stabSteps60 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric59 (offset degree : Nat) :
    (stabRaw59 offset degree).numeric =
      (fun table => (stabSteps59 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw60 offset degree).numeric (packedStep 42 degree table (17, false, [0, 1, 2, 3, 5, 6, 7, 9, 10, 13, 16], 17, (offset.testBit 59 ^^ true))) = _
  rw [stab_numeric60]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 58. -/
private noncomputable def stabRaw58 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [0, 2, 5, 6, 7, 10, 13, 16] (offset.testBit 58 ^^ false) (by decide) (stabRaw59 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps58 (offset : Nat) : List PackedStep := (17, true, [0, 2, 5, 6, 7, 10, 13, 16], 17, (offset.testBit 58 ^^ false)) :: stabSteps59 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric58 (offset degree : Nat) :
    (stabRaw58 offset degree).numeric =
      (fun table => (stabSteps58 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw59 offset degree).numeric (packedStep 42 degree table (17, true, [0, 2, 5, 6, 7, 10, 13, 16], 17, (offset.testBit 58 ^^ false))) = _
  rw [stab_numeric59]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 57. -/
private noncomputable def stabRaw57 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [3, 4, 5, 6, 11, 12, 13, 15] (offset.testBit 57 ^^ false) (by decide) (stabRaw58 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps57 (offset : Nat) : List PackedStep := (16, false, [3, 4, 5, 6, 11, 12, 13, 15], 16, (offset.testBit 57 ^^ false)) :: stabSteps58 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric57 (offset degree : Nat) :
    (stabRaw57 offset degree).numeric =
      (fun table => (stabSteps57 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw58 offset degree).numeric (packedStep 42 degree table (16, false, [3, 4, 5, 6, 11, 12, 13, 15], 16, (offset.testBit 57 ^^ false))) = _
  rw [stab_numeric58]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 56. -/
private noncomputable def stabRaw56 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [1, 2, 3, 5, 16] (offset.testBit 56 ^^ true) (by decide) (PackedProgram.forgetBitFast 1 (stabRaw57 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps56 (offset : Nat) : List PackedStep := (17, true, [1, 2, 3, 5, 16], 1, (offset.testBit 56 ^^ true)) :: stabSteps57 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric56 (offset degree : Nat) :
    (stabRaw56 offset degree).numeric =
      (fun table => (stabSteps56 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw57 offset degree).numeric (packedStep 42 degree table (17, true, [1, 2, 3, 5, 16], 1, (offset.testBit 56 ^^ true))) = _
  rw [stab_numeric57]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 55. -/
private noncomputable def stabRaw55 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [1, 2, 3, 4, 6, 13, 15] (offset.testBit 55 ^^ true) (by decide) (stabRaw56 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps55 (offset : Nat) : List PackedStep := (16, true, [1, 2, 3, 4, 6, 13, 15], 16, (offset.testBit 55 ^^ true)) :: stabSteps56 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric55 (offset degree : Nat) :
    (stabRaw55 offset degree).numeric =
      (fun table => (stabSteps55 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw56 offset degree).numeric (packedStep 42 degree table (16, true, [1, 2, 3, 4, 6, 13, 15], 16, (offset.testBit 55 ^^ true))) = _
  rw [stab_numeric56]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 54. -/
private noncomputable def stabRaw54 (offset degree : Nat) : PackedProgram 42 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [1, 2, 6, 13, 14] (offset.testBit 54 ^^ true) (by decide) (stabRaw55 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps54 (offset : Nat) : List PackedStep := (15, true, [1, 2, 6, 13, 14], 15, (offset.testBit 54 ^^ true)) :: stabSteps55 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric54 (offset degree : Nat) :
    (stabRaw54 offset degree).numeric =
      (fun table => (stabSteps54 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw55 offset degree).numeric (packedStep 42 degree table (15, true, [1, 2, 6, 13, 14], 15, (offset.testBit 54 ^^ true))) = _
  rw [stab_numeric55]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 53. -/
private noncomputable def stabRaw53 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [2, 3, 6, 7, 9, 10, 11, 13, 14] (offset.testBit 53 ^^ true) (by decide) (PackedProgram.forgetBitFast 7 (stabRaw54 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps53 (offset : Nat) : List PackedStep := (15, false, [2, 3, 6, 7, 9, 10, 11, 13, 14], 7, (offset.testBit 53 ^^ true)) :: stabSteps54 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric53 (offset degree : Nat) :
    (stabRaw53 offset degree).numeric =
      (fun table => (stabSteps53 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw54 offset degree).numeric (packedStep 42 degree table (15, false, [2, 3, 6, 7, 9, 10, 11, 13, 14], 7, (offset.testBit 53 ^^ true))) = _
  rw [stab_numeric54]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 52. -/
private noncomputable def stabRaw52 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [3, 4, 5, 6, 13, 15] (offset.testBit 52 ^^ false) (by decide) (PackedProgram.forgetBitFast 13 (stabRaw53 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps52 (offset : Nat) : List PackedStep := (16, false, [3, 4, 5, 6, 13, 15], 13, (offset.testBit 52 ^^ false)) :: stabSteps53 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric52 (offset degree : Nat) :
    (stabRaw52 offset degree).numeric =
      (fun table => (stabSteps52 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw53 offset degree).numeric (packedStep 42 degree table (16, false, [3, 4, 5, 6, 13, 15], 13, (offset.testBit 52 ^^ false))) = _
  rw [stab_numeric53]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 51. -/
private noncomputable def stabRaw51 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [2, 3, 6, 7, 10, 12, 13, 14, 15] (offset.testBit 51 ^^ true) (by decide) (stabRaw52 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps51 (offset : Nat) : List PackedStep := (16, false, [2, 3, 6, 7, 10, 12, 13, 14, 15], 16, (offset.testBit 51 ^^ true)) :: stabSteps52 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric51 (offset degree : Nat) :
    (stabRaw51 offset degree).numeric =
      (fun table => (stabSteps51 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw52 offset degree).numeric (packedStep 42 degree table (16, false, [2, 3, 6, 7, 10, 12, 13, 14, 15], 16, (offset.testBit 51 ^^ true))) = _
  rw [stab_numeric52]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 50. -/
private noncomputable def stabRaw50 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [0, 2, 3, 4, 7] (offset.testBit 50 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (stabRaw51 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps50 (offset : Nat) : List PackedStep := (17, false, [0, 2, 3, 4, 7], 0, (offset.testBit 50 ^^ true)) :: stabSteps51 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric50 (offset degree : Nat) :
    (stabRaw50 offset degree).numeric =
      (fun table => (stabSteps50 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw51 offset degree).numeric (packedStep 42 degree table (17, false, [0, 2, 3, 4, 7], 0, (offset.testBit 50 ^^ true))) = _
  rw [stab_numeric51]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 49. -/
private noncomputable def stabRaw49 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [0, 3, 4, 5, 6, 7, 15, 16, 17] (offset.testBit 49 ^^ true) (by decide) (PackedProgram.forgetBitFast 4 (stabRaw50 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps49 (offset : Nat) : List PackedStep := (18, true, [0, 3, 4, 5, 6, 7, 15, 16, 17], 4, (offset.testBit 49 ^^ true)) :: stabSteps50 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric49 (offset degree : Nat) :
    (stabRaw49 offset degree).numeric =
      (fun table => (stabSteps49 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw50 offset degree).numeric (packedStep 42 degree table (18, true, [0, 3, 4, 5, 6, 7, 15, 16, 17], 4, (offset.testBit 49 ^^ true))) = _
  rw [stab_numeric50]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 48. -/
private noncomputable def stabRaw48 (offset degree : Nat) : PackedProgram 42 degree 18 0 := PackedProgram.emit [0, 2, 4, 6, 9, 10, 12, 15] (offset.testBit 48 ^^ false) (by decide) (PackedProgram.forgetBitFast 9 (stabRaw49 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps48 (offset : Nat) : List PackedStep := (18, false, [0, 2, 4, 6, 9, 10, 12, 15], 9, (offset.testBit 48 ^^ false)) :: stabSteps49 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric48 (offset degree : Nat) :
    (stabRaw48 offset degree).numeric =
      (fun table => (stabSteps48 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw49 offset degree).numeric (packedStep 42 degree table (18, false, [0, 2, 4, 6, 9, 10, 12, 15], 9, (offset.testBit 48 ^^ false))) = _
  rw [stab_numeric49]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 47. -/
private noncomputable def stabRaw47 (offset degree : Nat) : PackedProgram 42 degree 18 0 := PackedProgram.read (width := 18) (PackedProgram.emit [0, 2, 3, 4, 12, 18] (offset.testBit 47 ^^ false) (by decide) (PackedProgram.forgetBitFast 12 (stabRaw48 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps47 (offset : Nat) : List PackedStep := (19, true, [0, 2, 3, 4, 12, 18], 12, (offset.testBit 47 ^^ false)) :: stabSteps48 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric47 (offset degree : Nat) :
    (stabRaw47 offset degree).numeric =
      (fun table => (stabSteps47 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw48 offset degree).numeric (packedStep 42 degree table (19, true, [0, 2, 3, 4, 12, 18], 12, (offset.testBit 47 ^^ false))) = _
  rw [stab_numeric48]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 46. -/
private noncomputable def stabRaw46 (offset degree : Nat) : PackedProgram 42 degree 18 0 := PackedProgram.emit [3, 4, 6, 7, 9, 10, 14, 15, 17] (offset.testBit 46 ^^ true) (by decide) (stabRaw47 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps46 (offset : Nat) : List PackedStep := (18, false, [3, 4, 6, 7, 9, 10, 14, 15, 17], 18, (offset.testBit 46 ^^ true)) :: stabSteps47 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric46 (offset degree : Nat) :
    (stabRaw46 offset degree).numeric =
      (fun table => (stabSteps46 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw47 offset degree).numeric (packedStep 42 degree table (18, false, [3, 4, 6, 7, 9, 10, 14, 15, 17], 18, (offset.testBit 46 ^^ true))) = _
  rw [stab_numeric47]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 45. -/
private noncomputable def stabRaw45 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [3, 7, 8, 10, 11, 12, 14, 15, 17] (offset.testBit 45 ^^ true) (by decide) (stabRaw46 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps45 (offset : Nat) : List PackedStep := (18, true, [3, 7, 8, 10, 11, 12, 14, 15, 17], 18, (offset.testBit 45 ^^ true)) :: stabSteps46 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric45 (offset degree : Nat) :
    (stabRaw45 offset degree).numeric =
      (fun table => (stabSteps45 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw46 offset degree).numeric (packedStep 42 degree table (18, true, [3, 7, 8, 10, 11, 12, 14, 15, 17], 18, (offset.testBit 45 ^^ true))) = _
  rw [stab_numeric46]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 44. -/
private noncomputable def stabRaw44 (offset degree : Nat) : PackedProgram 42 degree 18 0 := PackedProgram.emit [3, 6, 8, 10, 12, 15] (offset.testBit 44 ^^ false) (by decide) (PackedProgram.forgetBitFast 8 (stabRaw45 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps44 (offset : Nat) : List PackedStep := (18, false, [3, 6, 8, 10, 12, 15], 8, (offset.testBit 44 ^^ false)) :: stabSteps45 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric44 (offset degree : Nat) :
    (stabRaw44 offset degree).numeric =
      (fun table => (stabSteps44 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw45 offset degree).numeric (packedStep 42 degree table (18, false, [3, 6, 8, 10, 12, 15], 8, (offset.testBit 44 ^^ false))) = _
  rw [stab_numeric45]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 43. -/
private noncomputable def stabRaw43 (offset degree : Nat) : PackedProgram 42 degree 18 0 := PackedProgram.emit [6, 8, 11, 12, 13, 17] (offset.testBit 43 ^^ false) (by decide) (stabRaw44 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps43 (offset : Nat) : List PackedStep := (18, false, [6, 8, 11, 12, 13, 17], 18, (offset.testBit 43 ^^ false)) :: stabSteps44 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric43 (offset degree : Nat) :
    (stabRaw43 offset degree).numeric =
      (fun table => (stabSteps43 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw44 offset degree).numeric (packedStep 42 degree table (18, false, [6, 8, 11, 12, 13, 17], 18, (offset.testBit 43 ^^ false))) = _
  rw [stab_numeric44]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 42. -/
private noncomputable def stabRaw42 (offset degree : Nat) : PackedProgram 42 degree 18 0 := PackedProgram.read (width := 18) (PackedProgram.emit [0, 2, 3, 6, 10, 14, 15, 18] (offset.testBit 42 ^^ false) (by decide) (PackedProgram.forgetBitFast 10 (stabRaw43 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps42 (offset : Nat) : List PackedStep := (19, true, [0, 2, 3, 6, 10, 14, 15, 18], 10, (offset.testBit 42 ^^ false)) :: stabSteps43 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric42 (offset degree : Nat) :
    (stabRaw42 offset degree).numeric =
      (fun table => (stabSteps42 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw43 offset degree).numeric (packedStep 42 degree table (19, true, [0, 2, 3, 6, 10, 14, 15, 18], 10, (offset.testBit 42 ^^ false))) = _
  rw [stab_numeric43]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 41. -/
private noncomputable def stabRaw41 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [3, 6, 7, 10, 17] (offset.testBit 41 ^^ true) (by decide) (stabRaw42 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps41 (offset : Nat) : List PackedStep := (18, true, [3, 6, 7, 10, 17], 18, (offset.testBit 41 ^^ true)) :: stabSteps42 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric41 (offset degree : Nat) :
    (stabRaw41 offset degree).numeric =
      (fun table => (stabSteps41 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw42 offset degree).numeric (packedStep 42 degree table (18, true, [3, 6, 7, 10, 17], 18, (offset.testBit 41 ^^ true))) = _
  rw [stab_numeric42]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 40. -/
private noncomputable def stabRaw40 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [3, 5, 6, 7, 8, 12, 15, 16] (offset.testBit 40 ^^ false) (by decide) (stabRaw41 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps40 (offset : Nat) : List PackedStep := (17, false, [3, 5, 6, 7, 8, 12, 15, 16], 17, (offset.testBit 40 ^^ false)) :: stabSteps41 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric40 (offset degree : Nat) :
    (stabRaw40 offset degree).numeric =
      (fun table => (stabSteps40 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw41 offset degree).numeric (packedStep 42 degree table (17, false, [3, 5, 6, 7, 8, 12, 15, 16], 17, (offset.testBit 40 ^^ false))) = _
  rw [stab_numeric41]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 39. -/
private noncomputable def stabRaw39 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [0, 4, 7, 9, 10, 16] (offset.testBit 39 ^^ false) (by decide) (stabRaw40 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps39 (offset : Nat) : List PackedStep := (17, true, [0, 4, 7, 9, 10, 16], 17, (offset.testBit 39 ^^ false)) :: stabSteps40 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric39 (offset degree : Nat) :
    (stabRaw39 offset degree).numeric =
      (fun table => (stabSteps39 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw40 offset degree).numeric (packedStep 42 degree table (17, true, [0, 4, 7, 9, 10, 16], 17, (offset.testBit 39 ^^ false))) = _
  rw [stab_numeric40]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 38. -/
private noncomputable def stabRaw38 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [3, 7, 8, 11, 12, 16] (offset.testBit 38 ^^ false) (by decide) (PackedProgram.forgetBitFast 11 (stabRaw39 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps38 (offset : Nat) : List PackedStep := (17, true, [3, 7, 8, 11, 12, 16], 11, (offset.testBit 38 ^^ false)) :: stabSteps39 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric38 (offset degree : Nat) :
    (stabRaw38 offset degree).numeric =
      (fun table => (stabSteps38 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw39 offset degree).numeric (packedStep 42 degree table (17, true, [3, 7, 8, 11, 12, 16], 11, (offset.testBit 38 ^^ false))) = _
  rw [stab_numeric39]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 37. -/
private noncomputable def stabRaw37 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [0, 2, 4, 5, 6, 7, 8, 11, 15] (offset.testBit 37 ^^ true) (by decide) (stabRaw38 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps37 (offset : Nat) : List PackedStep := (16, true, [0, 2, 4, 5, 6, 7, 8, 11, 15], 16, (offset.testBit 37 ^^ true)) :: stabSteps38 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric37 (offset degree : Nat) :
    (stabRaw37 offset degree).numeric =
      (fun table => (stabSteps37 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw38 offset degree).numeric (packedStep 42 degree table (16, true, [0, 2, 4, 5, 6, 7, 8, 11, 15], 16, (offset.testBit 37 ^^ true))) = _
  rw [stab_numeric38]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 36. -/
private noncomputable def stabRaw36 (offset degree : Nat) : PackedProgram 42 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [0, 2, 4, 8, 11, 12, 14] (offset.testBit 36 ^^ true) (by decide) (stabRaw37 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps36 (offset : Nat) : List PackedStep := (15, true, [0, 2, 4, 8, 11, 12, 14], 15, (offset.testBit 36 ^^ true)) :: stabSteps37 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric36 (offset degree : Nat) :
    (stabRaw36 offset degree).numeric =
      (fun table => (stabSteps36 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw37 offset degree).numeric (packedStep 42 degree table (15, true, [0, 2, 4, 8, 11, 12, 14], 15, (offset.testBit 36 ^^ true))) = _
  rw [stab_numeric37]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 35. -/
private noncomputable def stabRaw35 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [2, 3, 6, 7, 12] (offset.testBit 35 ^^ true) (by decide) (PackedProgram.forgetBitFast 7 (stabRaw36 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps35 (offset : Nat) : List PackedStep := (15, false, [2, 3, 6, 7, 12], 7, (offset.testBit 35 ^^ true)) :: stabSteps36 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric35 (offset degree : Nat) :
    (stabRaw35 offset degree).numeric =
      (fun table => (stabSteps35 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw36 offset degree).numeric (packedStep 42 degree table (15, false, [2, 3, 6, 7, 12], 7, (offset.testBit 35 ^^ true))) = _
  rw [stab_numeric36]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 34. -/
private noncomputable def stabRaw34 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [0, 1, 2, 3, 5, 8, 12, 13] (offset.testBit 34 ^^ false) (by decide) (PackedProgram.forgetBitFast 13 (stabRaw35 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps34 (offset : Nat) : List PackedStep := (16, false, [0, 1, 2, 3, 5, 8, 12, 13], 13, (offset.testBit 34 ^^ false)) :: stabSteps35 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric34 (offset degree : Nat) :
    (stabRaw34 offset degree).numeric =
      (fun table => (stabSteps34 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw35 offset degree).numeric (packedStep 42 degree table (16, false, [0, 1, 2, 3, 5, 8, 12, 13], 13, (offset.testBit 34 ^^ false))) = _
  rw [stab_numeric35]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 33. -/
private noncomputable def stabRaw33 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [0, 1, 2, 3, 4, 5, 6, 8, 12, 13] (offset.testBit 33 ^^ false) (by decide) (stabRaw34 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps33 (offset : Nat) : List PackedStep := (16, false, [0, 1, 2, 3, 4, 5, 6, 8, 12, 13], 16, (offset.testBit 33 ^^ false)) :: stabSteps34 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric33 (offset degree : Nat) :
    (stabRaw33 offset degree).numeric =
      (fun table => (stabSteps33 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw34 offset degree).numeric (packedStep 42 degree table (16, false, [0, 1, 2, 3, 4, 5, 6, 8, 12, 13], 16, (offset.testBit 33 ^^ false))) = _
  rw [stab_numeric34]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 32. -/
private noncomputable def stabRaw32 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [2, 3, 7, 10] (offset.testBit 32 ^^ false) (by decide) (stabRaw33 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps32 (offset : Nat) : List PackedStep := (16, false, [2, 3, 7, 10], 16, (offset.testBit 32 ^^ false)) :: stabSteps33 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric32 (offset degree : Nat) :
    (stabRaw32 offset degree).numeric =
      (fun table => (stabSteps32 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw33 offset degree).numeric (packedStep 42 degree table (16, false, [2, 3, 7, 10], 16, (offset.testBit 32 ^^ false))) = _
  rw [stab_numeric33]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 31. -/
private noncomputable def stabRaw31 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [4, 6, 12, 16] (offset.testBit 31 ^^ false) (by decide) (PackedProgram.forgetBitFast 6 (stabRaw32 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps31 (offset : Nat) : List PackedStep := (17, true, [4, 6, 12, 16], 6, (offset.testBit 31 ^^ false)) :: stabSteps32 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric31 (offset degree : Nat) :
    (stabRaw31 offset degree).numeric =
      (fun table => (stabSteps31 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw32 offset degree).numeric (packedStep 42 degree table (17, true, [4, 6, 12, 16], 6, (offset.testBit 31 ^^ false))) = _
  rw [stab_numeric32]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 30. -/
private noncomputable def stabRaw30 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [3, 6, 9, 15] (offset.testBit 30 ^^ false) (by decide) (PackedProgram.forgetBitFast 3 (stabRaw31 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps30 (offset : Nat) : List PackedStep := (17, false, [3, 6, 9, 15], 3, (offset.testBit 30 ^^ false)) :: stabSteps31 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric30 (offset degree : Nat) :
    (stabRaw30 offset degree).numeric =
      (fun table => (stabSteps30 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw31 offset degree).numeric (packedStep 42 degree table (17, false, [3, 6, 9, 15], 3, (offset.testBit 30 ^^ false))) = _
  rw [stab_numeric31]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 29. -/
private noncomputable def stabRaw29 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [0, 1, 2, 4, 5, 7, 8, 13, 14, 15, 16] (offset.testBit 29 ^^ true) (by decide) (stabRaw30 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps29 (offset : Nat) : List PackedStep := (17, false, [0, 1, 2, 4, 5, 7, 8, 13, 14, 15, 16], 17, (offset.testBit 29 ^^ true)) :: stabSteps30 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric29 (offset degree : Nat) :
    (stabRaw29 offset degree).numeric =
      (fun table => (stabSteps29 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw30 offset degree).numeric (packedStep 42 degree table (17, false, [0, 1, 2, 4, 5, 7, 8, 13, 14, 15, 16], 17, (offset.testBit 29 ^^ true))) = _
  rw [stab_numeric30]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 28. -/
private noncomputable def stabRaw28 (offset degree : Nat) : PackedProgram 42 degree 17 0 := PackedProgram.emit [0, 1, 2, 3, 12, 14, 16] (offset.testBit 28 ^^ true) (by decide) (stabRaw29 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps28 (offset : Nat) : List PackedStep := (17, false, [0, 1, 2, 3, 12, 14, 16], 17, (offset.testBit 28 ^^ true)) :: stabSteps29 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric28 (offset degree : Nat) :
    (stabRaw28 offset degree).numeric =
      (fun table => (stabSteps28 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw29 offset degree).numeric (packedStep 42 degree table (17, false, [0, 1, 2, 3, 12, 14, 16], 17, (offset.testBit 28 ^^ true))) = _
  rw [stab_numeric29]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 27. -/
private noncomputable def stabRaw27 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [0, 3, 4, 6, 14, 16] (offset.testBit 27 ^^ false) (by decide) (stabRaw28 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps27 (offset : Nat) : List PackedStep := (17, true, [0, 3, 4, 6, 14, 16], 17, (offset.testBit 27 ^^ false)) :: stabSteps28 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric27 (offset degree : Nat) :
    (stabRaw27 offset degree).numeric =
      (fun table => (stabSteps27 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw28 offset degree).numeric (packedStep 42 degree table (17, true, [0, 3, 4, 6, 14, 16], 17, (offset.testBit 27 ^^ false))) = _
  rw [stab_numeric28]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 26. -/
private noncomputable def stabRaw26 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [3, 4, 8, 11, 15] (offset.testBit 26 ^^ true) (by decide) (stabRaw27 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps26 (offset : Nat) : List PackedStep := (16, true, [3, 4, 8, 11, 15], 16, (offset.testBit 26 ^^ true)) :: stabSteps27 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric26 (offset degree : Nat) :
    (stabRaw26 offset degree).numeric =
      (fun table => (stabSteps26 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw27 offset degree).numeric (packedStep 42 degree table (16, true, [3, 4, 8, 11, 15], 16, (offset.testBit 26 ^^ true))) = _
  rw [stab_numeric27]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 25. -/
private noncomputable def stabRaw25 (offset degree : Nat) : PackedProgram 42 degree 16 0 := PackedProgram.emit [7, 9, 11, 12, 14, 15] (offset.testBit 25 ^^ false) (by decide) (PackedProgram.forgetBitFast 14 (stabRaw26 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps25 (offset : Nat) : List PackedStep := (16, false, [7, 9, 11, 12, 14, 15], 14, (offset.testBit 25 ^^ false)) :: stabSteps26 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric25 (offset degree : Nat) :
    (stabRaw25 offset degree).numeric =
      (fun table => (stabSteps25 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw26 offset degree).numeric (packedStep 42 degree table (16, false, [7, 9, 11, 12, 14, 15], 14, (offset.testBit 25 ^^ false))) = _
  rw [stab_numeric26]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 24. -/
private noncomputable def stabRaw24 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [7, 8, 14, 15] (offset.testBit 24 ^^ false) (by decide) (stabRaw25 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps24 (offset : Nat) : List PackedStep := (16, true, [7, 8, 14, 15], 16, (offset.testBit 24 ^^ false)) :: stabSteps25 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric24 (offset degree : Nat) :
    (stabRaw24 offset degree).numeric =
      (fun table => (stabSteps24 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw25 offset degree).numeric (packedStep 42 degree table (16, true, [7, 8, 14, 15], 16, (offset.testBit 24 ^^ false))) = _
  rw [stab_numeric25]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 23. -/
private noncomputable def stabRaw23 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [0, 3, 4, 5, 6, 7, 8, 14] (offset.testBit 23 ^^ false) (by decide) (stabRaw24 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps23 (offset : Nat) : List PackedStep := (15, false, [0, 3, 4, 5, 6, 7, 8, 14], 15, (offset.testBit 23 ^^ false)) :: stabSteps24 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric23 (offset degree : Nat) :
    (stabRaw23 offset degree).numeric =
      (fun table => (stabSteps23 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw24 offset degree).numeric (packedStep 42 degree table (15, false, [0, 3, 4, 5, 6, 7, 8, 14], 15, (offset.testBit 23 ^^ false))) = _
  rw [stab_numeric24]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 22. -/
private noncomputable def stabRaw22 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [0, 1, 4, 5, 7, 12, 13, 14] (offset.testBit 22 ^^ false) (by decide) (stabRaw23 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps22 (offset : Nat) : List PackedStep := (15, false, [0, 1, 4, 5, 7, 12, 13, 14], 15, (offset.testBit 22 ^^ false)) :: stabSteps23 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric22 (offset degree : Nat) :
    (stabRaw22 offset degree).numeric =
      (fun table => (stabSteps22 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw23 offset degree).numeric (packedStep 42 degree table (15, false, [0, 1, 4, 5, 7, 12, 13, 14], 15, (offset.testBit 22 ^^ false))) = _
  rw [stab_numeric23]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 21. -/
private noncomputable def stabRaw21 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [0, 2, 3, 7, 8, 12, 14] (offset.testBit 21 ^^ true) (by decide) (stabRaw22 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps21 (offset : Nat) : List PackedStep := (15, false, [0, 2, 3, 7, 8, 12, 14], 15, (offset.testBit 21 ^^ true)) :: stabSteps22 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric21 (offset degree : Nat) :
    (stabRaw21 offset degree).numeric =
      (fun table => (stabSteps21 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw22 offset degree).numeric (packedStep 42 degree table (15, false, [0, 2, 3, 7, 8, 12, 14], 15, (offset.testBit 21 ^^ true))) = _
  rw [stab_numeric22]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 20. -/
private noncomputable def stabRaw20 (offset degree : Nat) : PackedProgram 42 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [14] (offset.testBit 20 ^^ true) (by decide) (stabRaw21 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps20 (offset : Nat) : List PackedStep := (15, true, [14], 15, (offset.testBit 20 ^^ true)) :: stabSteps21 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric20 (offset degree : Nat) :
    (stabRaw20 offset degree).numeric =
      (fun table => (stabSteps20 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw21 offset degree).numeric (packedStep 42 degree table (15, true, [14], 15, (offset.testBit 20 ^^ true))) = _
  rw [stab_numeric21]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 19. -/
private noncomputable def stabRaw19 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.emit [0, 1, 2, 5, 13] (offset.testBit 19 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (stabRaw20 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps19 (offset : Nat) : List PackedStep := (15, false, [0, 1, 2, 5, 13], 0, (offset.testBit 19 ^^ true)) :: stabSteps20 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric19 (offset degree : Nat) :
    (stabRaw19 offset degree).numeric =
      (fun table => (stabSteps19 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw20 offset degree).numeric (packedStep 42 degree table (15, false, [0, 1, 2, 5, 13], 0, (offset.testBit 19 ^^ true))) = _
  rw [stab_numeric20]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 18. -/
private noncomputable def stabRaw18 (offset degree : Nat) : PackedProgram 42 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [0, 2, 4, 8, 12, 14, 15] (offset.testBit 18 ^^ true) (by decide) (PackedProgram.forgetBitFast 2 (stabRaw19 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps18 (offset : Nat) : List PackedStep := (16, true, [0, 2, 4, 8, 12, 14, 15], 2, (offset.testBit 18 ^^ true)) :: stabSteps19 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric18 (offset degree : Nat) :
    (stabRaw18 offset degree).numeric =
      (fun table => (stabSteps18 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw19 offset degree).numeric (packedStep 42 degree table (16, true, [0, 2, 4, 8, 12, 14, 15], 2, (offset.testBit 18 ^^ true))) = _
  rw [stab_numeric19]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 17. -/
private noncomputable def stabRaw17 (offset degree : Nat) : PackedProgram 42 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [0, 4, 8, 12, 14] (offset.testBit 17 ^^ true) (by decide) (stabRaw18 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps17 (offset : Nat) : List PackedStep := (15, true, [0, 4, 8, 12, 14], 15, (offset.testBit 17 ^^ true)) :: stabSteps18 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric17 (offset degree : Nat) :
    (stabRaw17 offset degree).numeric =
      (fun table => (stabSteps17 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw18 offset degree).numeric (packedStep 42 degree table (15, true, [0, 4, 8, 12, 14], 15, (offset.testBit 17 ^^ true))) = _
  rw [stab_numeric18]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 16. -/
private noncomputable def stabRaw16 (offset degree : Nat) : PackedProgram 42 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [1, 12, 14] (offset.testBit 16 ^^ true) (by decide) (PackedProgram.forgetBitFast 1 (stabRaw17 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps16 (offset : Nat) : List PackedStep := (15, true, [1, 12, 14], 1, (offset.testBit 16 ^^ true)) :: stabSteps17 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric16 (offset degree : Nat) :
    (stabRaw16 offset degree).numeric =
      (fun table => (stabSteps16 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw17 offset degree).numeric (packedStep 42 degree table (15, true, [1, 12, 14], 1, (offset.testBit 16 ^^ true))) = _
  rw [stab_numeric17]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 15. -/
private noncomputable def stabRaw15 (offset degree : Nat) : PackedProgram 42 degree 13 0 := PackedProgram.read (width := 13) (PackedProgram.emit [0, 2, 13] (offset.testBit 15 ^^ true) (by decide) (stabRaw16 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps15 (offset : Nat) : List PackedStep := (14, true, [0, 2, 13], 14, (offset.testBit 15 ^^ true)) :: stabSteps16 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric15 (offset degree : Nat) :
    (stabRaw15 offset degree).numeric =
      (fun table => (stabSteps15 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw16 offset degree).numeric (packedStep 42 degree table (14, true, [0, 2, 13], 14, (offset.testBit 15 ^^ true))) = _
  rw [stab_numeric16]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 14. -/
private noncomputable def stabRaw14 (offset degree : Nat) : PackedProgram 42 degree 13 0 := PackedProgram.read (width := 13) (PackedProgram.emit [5, 7, 12, 13] (offset.testBit 14 ^^ false) (by decide) (PackedProgram.forgetBitFast 5 (stabRaw15 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps14 (offset : Nat) : List PackedStep := (14, true, [5, 7, 12, 13], 5, (offset.testBit 14 ^^ false)) :: stabSteps15 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric14 (offset degree : Nat) :
    (stabRaw14 offset degree).numeric =
      (fun table => (stabSteps14 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw15 offset degree).numeric (packedStep 42 degree table (14, true, [5, 7, 12, 13], 5, (offset.testBit 14 ^^ false))) = _
  rw [stab_numeric15]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 13. -/
private noncomputable def stabRaw13 (offset degree : Nat) : PackedProgram 42 degree 12 0 := PackedProgram.read (width := 12) (PackedProgram.emit [1, 5, 12] (offset.testBit 13 ^^ true) (by decide) (stabRaw14 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps13 (offset : Nat) : List PackedStep := (13, true, [1, 5, 12], 13, (offset.testBit 13 ^^ true)) :: stabSteps14 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric13 (offset degree : Nat) :
    (stabRaw13 offset degree).numeric =
      (fun table => (stabSteps13 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw14 offset degree).numeric (packedStep 42 degree table (13, true, [1, 5, 12], 13, (offset.testBit 13 ^^ true))) = _
  rw [stab_numeric14]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 12. -/
private noncomputable def stabRaw12 (offset degree : Nat) : PackedProgram 42 degree 11 0 := PackedProgram.read (width := 11) (PackedProgram.emit [0, 2, 5, 11] (offset.testBit 12 ^^ false) (by decide) (stabRaw13 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps12 (offset : Nat) : List PackedStep := (12, true, [0, 2, 5, 11], 12, (offset.testBit 12 ^^ false)) :: stabSteps13 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric12 (offset degree : Nat) :
    (stabRaw12 offset degree).numeric =
      (fun table => (stabSteps12 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw13 offset degree).numeric (packedStep 42 degree table (12, true, [0, 2, 5, 11], 12, (offset.testBit 12 ^^ false))) = _
  rw [stab_numeric13]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 11. -/
private noncomputable def stabRaw11 (offset degree : Nat) : PackedProgram 42 degree 11 0 := PackedProgram.emit [0, 3, 4, 8, 10] (offset.testBit 11 ^^ true) (by decide) (stabRaw12 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps11 (offset : Nat) : List PackedStep := (11, false, [0, 3, 4, 8, 10], 11, (offset.testBit 11 ^^ true)) :: stabSteps12 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric11 (offset degree : Nat) :
    (stabRaw11 offset degree).numeric =
      (fun table => (stabSteps11 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw12 offset degree).numeric (packedStep 42 degree table (11, false, [0, 3, 4, 8, 10], 11, (offset.testBit 11 ^^ true))) = _
  rw [stab_numeric12]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 10. -/
private noncomputable def stabRaw10 (offset degree : Nat) : PackedProgram 42 degree 10 0 := PackedProgram.read (width := 10) (PackedProgram.emit [5, 10] (offset.testBit 10 ^^ false) (by decide) (stabRaw11 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps10 (offset : Nat) : List PackedStep := (11, true, [5, 10], 11, (offset.testBit 10 ^^ false)) :: stabSteps11 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric10 (offset degree : Nat) :
    (stabRaw10 offset degree).numeric =
      (fun table => (stabSteps10 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw11 offset degree).numeric (packedStep 42 degree table (11, true, [5, 10], 11, (offset.testBit 10 ^^ false))) = _
  rw [stab_numeric11]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 9. -/
private noncomputable def stabRaw9 (offset degree : Nat) : PackedProgram 42 degree 9 0 := PackedProgram.read (width := 9) (PackedProgram.emit [0, 1, 8, 9] (offset.testBit 9 ^^ false) (by decide) (stabRaw10 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps9 (offset : Nat) : List PackedStep := (10, true, [0, 1, 8, 9], 10, (offset.testBit 9 ^^ false)) :: stabSteps10 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric9 (offset degree : Nat) :
    (stabRaw9 offset degree).numeric =
      (fun table => (stabSteps9 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw10 offset degree).numeric (packedStep 42 degree table (10, true, [0, 1, 8, 9], 10, (offset.testBit 9 ^^ false))) = _
  rw [stab_numeric10]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 8. -/
private noncomputable def stabRaw8 (offset degree : Nat) : PackedProgram 42 degree 8 0 := PackedProgram.read (width := 8) (PackedProgram.emit [0, 2, 3, 6, 8] (offset.testBit 8 ^^ true) (by decide) (stabRaw9 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps8 (offset : Nat) : List PackedStep := (9, true, [0, 2, 3, 6, 8], 9, (offset.testBit 8 ^^ true)) :: stabSteps9 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric8 (offset degree : Nat) :
    (stabRaw8 offset degree).numeric =
      (fun table => (stabSteps8 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw9 offset degree).numeric (packedStep 42 degree table (9, true, [0, 2, 3, 6, 8], 9, (offset.testBit 8 ^^ true))) = _
  rw [stab_numeric9]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 7. -/
private noncomputable def stabRaw7 (offset degree : Nat) : PackedProgram 42 degree 7 0 := PackedProgram.read (width := 7) (PackedProgram.emit [1, 7] (offset.testBit 7 ^^ false) (by decide) (stabRaw8 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps7 (offset : Nat) : List PackedStep := (8, true, [1, 7], 8, (offset.testBit 7 ^^ false)) :: stabSteps8 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric7 (offset degree : Nat) :
    (stabRaw7 offset degree).numeric =
      (fun table => (stabSteps7 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw8 offset degree).numeric (packedStep 42 degree table (8, true, [1, 7], 8, (offset.testBit 7 ^^ false))) = _
  rw [stab_numeric8]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 6. -/
private noncomputable def stabRaw6 (offset degree : Nat) : PackedProgram 42 degree 6 0 := PackedProgram.read (width := 6) (PackedProgram.emit [3, 5, 6] (offset.testBit 6 ^^ true) (by decide) (stabRaw7 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps6 (offset : Nat) : List PackedStep := (7, true, [3, 5, 6], 7, (offset.testBit 6 ^^ true)) :: stabSteps7 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric6 (offset degree : Nat) :
    (stabRaw6 offset degree).numeric =
      (fun table => (stabSteps6 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw7 offset degree).numeric (packedStep 42 degree table (7, true, [3, 5, 6], 7, (offset.testBit 6 ^^ true))) = _
  rw [stab_numeric7]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 5. -/
private noncomputable def stabRaw5 (offset degree : Nat) : PackedProgram 42 degree 5 0 := PackedProgram.read (width := 5) (PackedProgram.emit [5] (offset.testBit 5 ^^ true) (by decide) (stabRaw6 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps5 (offset : Nat) : List PackedStep := (6, true, [5], 6, (offset.testBit 5 ^^ true)) :: stabSteps6 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric5 (offset degree : Nat) :
    (stabRaw5 offset degree).numeric =
      (fun table => (stabSteps5 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw6 offset degree).numeric (packedStep 42 degree table (6, true, [5], 6, (offset.testBit 5 ^^ true))) = _
  rw [stab_numeric6]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 4. -/
private noncomputable def stabRaw4 (offset degree : Nat) : PackedProgram 42 degree 4 0 := PackedProgram.read (width := 4) (PackedProgram.emit [0, 2, 4] (offset.testBit 4 ^^ true) (by decide) (stabRaw5 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps4 (offset : Nat) : List PackedStep := (5, true, [0, 2, 4], 5, (offset.testBit 4 ^^ true)) :: stabSteps5 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric4 (offset degree : Nat) :
    (stabRaw4 offset degree).numeric =
      (fun table => (stabSteps4 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw5 offset degree).numeric (packedStep 42 degree table (5, true, [0, 2, 4], 5, (offset.testBit 4 ^^ true))) = _
  rw [stab_numeric5]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 3. -/
private noncomputable def stabRaw3 (offset degree : Nat) : PackedProgram 42 degree 3 0 := PackedProgram.read (width := 3) (PackedProgram.emit [1, 3] (offset.testBit 3 ^^ false) (by decide) (stabRaw4 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps3 (offset : Nat) : List PackedStep := (4, true, [1, 3], 4, (offset.testBit 3 ^^ false)) :: stabSteps4 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric3 (offset degree : Nat) :
    (stabRaw3 offset degree).numeric =
      (fun table => (stabSteps3 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw4 offset degree).numeric (packedStep 42 degree table (4, true, [1, 3], 4, (offset.testBit 3 ^^ false))) = _
  rw [stab_numeric4]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 2. -/
private noncomputable def stabRaw2 (offset degree : Nat) : PackedProgram 42 degree 2 0 := PackedProgram.read (width := 2) (PackedProgram.emit [2] (offset.testBit 2 ^^ true) (by decide) (stabRaw3 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps2 (offset : Nat) : List PackedStep := (3, true, [2], 3, (offset.testBit 2 ^^ true)) :: stabSteps3 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric2 (offset degree : Nat) :
    (stabRaw2 offset degree).numeric =
      (fun table => (stabSteps2 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw3 offset degree).numeric (packedStep 42 degree table (3, true, [2], 3, (offset.testBit 2 ^^ true))) = _
  rw [stab_numeric3]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 1. -/
private noncomputable def stabRaw1 (offset degree : Nat) : PackedProgram 42 degree 1 0 := PackedProgram.read (width := 1) (PackedProgram.emit [1] (offset.testBit 1 ^^ true) (by decide) (stabRaw2 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps1 (offset : Nat) : List PackedStep := (2, true, [1], 2, (offset.testBit 1 ^^ true)) :: stabSteps2 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric1 (offset degree : Nat) :
    (stabRaw1 offset degree).numeric =
      (fun table => (stabSteps1 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw2 offset degree).numeric (packedStep 42 degree table (2, true, [1], 2, (offset.testBit 1 ^^ true))) = _
  rw [stab_numeric2]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 0. -/
private noncomputable def stabRaw0 (offset degree : Nat) : PackedProgram 42 degree 0 0 := PackedProgram.read (width := 0) (PackedProgram.emit [0] (offset.testBit 0 ^^ true) (by decide) (stabRaw1 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def stabSteps0 (offset : Nat) : List PackedStep := (1, true, [0], 1, (offset.testBit 0 ^^ true)) :: stabSteps1 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem stab_numeric0 (offset degree : Nat) :
    (stabRaw0 offset degree).numeric =
      (fun table => (stabSteps0 offset).foldl (packedStep 42 degree) table) := by
  funext table
  change (stabRaw1 offset degree).numeric (packedStep 42 degree table (1, true, [0], 1, (offset.testBit 0 ^^ true))) = _
  rw [stab_numeric1]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata for the entire fast recurrence. -/
noncomputable def stabSteps (offset : Nat) : List PackedStep := stabSteps0 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Flattened affine instruction list for the certified encoder. -/
noncomputable def stabInstructions (offset : Nat) : List Instruction := [
  .read 0,
  .emit [0] (offset.testBit 0 ^^ true),
  .read 1,
  .emit [1] (offset.testBit 1 ^^ true),
  .read 2,
  .emit [2] (offset.testBit 2 ^^ true),
  .read 3,
  .emit [1, 3] (offset.testBit 3 ^^ false),
  .read 4,
  .emit [0, 2, 4] (offset.testBit 4 ^^ true),
  .read 5,
  .emit [5] (offset.testBit 5 ^^ true),
  .read 6,
  .emit [3, 5, 6] (offset.testBit 6 ^^ true),
  .read 7,
  .emit [1, 7] (offset.testBit 7 ^^ false),
  .read 8,
  .emit [0, 2, 3, 6, 8] (offset.testBit 8 ^^ true),
  .read 9,
  .emit [0, 1, 8, 9] (offset.testBit 9 ^^ false),
  .read 10,
  .emit [5, 10] (offset.testBit 10 ^^ false),
  .emit [0, 3, 4, 8, 10] (offset.testBit 11 ^^ true),
  .read 11,
  .emit [0, 2, 5, 11] (offset.testBit 12 ^^ false),
  .read 12,
  .emit [1, 5, 12] (offset.testBit 13 ^^ true),
  .read 13,
  .emit [5, 7, 12, 13] (offset.testBit 14 ^^ false),
  .forget 5 14,
  .read 13,
  .emit [0, 2, 13] (offset.testBit 15 ^^ true),
  .read 14,
  .emit [1, 12, 14] (offset.testBit 16 ^^ true),
  .forget 1 15,
  .read 14,
  .emit [0, 4, 8, 12, 14] (offset.testBit 17 ^^ true),
  .read 15,
  .emit [0, 2, 4, 8, 12, 14, 15] (offset.testBit 18 ^^ true),
  .forget 2 16,
  .emit [0, 1, 2, 5, 13] (offset.testBit 19 ^^ true),
  .forget 0 15,
  .read 14,
  .emit [14] (offset.testBit 20 ^^ true),
  .emit [0, 2, 3, 7, 8, 12, 14] (offset.testBit 21 ^^ true),
  .emit [0, 1, 4, 5, 7, 12, 13, 14] (offset.testBit 22 ^^ false),
  .emit [0, 3, 4, 5, 6, 7, 8, 14] (offset.testBit 23 ^^ false),
  .read 15,
  .emit [7, 8, 14, 15] (offset.testBit 24 ^^ false),
  .emit [7, 9, 11, 12, 14, 15] (offset.testBit 25 ^^ false),
  .forget 14 16,
  .read 15,
  .emit [3, 4, 8, 11, 15] (offset.testBit 26 ^^ true),
  .read 16,
  .emit [0, 3, 4, 6, 14, 16] (offset.testBit 27 ^^ false),
  .emit [0, 1, 2, 3, 12, 14, 16] (offset.testBit 28 ^^ true),
  .emit [0, 1, 2, 4, 5, 7, 8, 13, 14, 15, 16] (offset.testBit 29 ^^ true),
  .emit [3, 6, 9, 15] (offset.testBit 30 ^^ false),
  .forget 3 17,
  .read 16,
  .emit [4, 6, 12, 16] (offset.testBit 31 ^^ false),
  .forget 6 17,
  .emit [2, 3, 7, 10] (offset.testBit 32 ^^ false),
  .emit [0, 1, 2, 3, 4, 5, 6, 8, 12, 13] (offset.testBit 33 ^^ false),
  .emit [0, 1, 2, 3, 5, 8, 12, 13] (offset.testBit 34 ^^ false),
  .forget 13 16,
  .emit [2, 3, 6, 7, 12] (offset.testBit 35 ^^ true),
  .forget 7 15,
  .read 14,
  .emit [0, 2, 4, 8, 11, 12, 14] (offset.testBit 36 ^^ true),
  .read 15,
  .emit [0, 2, 4, 5, 6, 7, 8, 11, 15] (offset.testBit 37 ^^ true),
  .read 16,
  .emit [3, 7, 8, 11, 12, 16] (offset.testBit 38 ^^ false),
  .forget 11 17,
  .read 16,
  .emit [0, 4, 7, 9, 10, 16] (offset.testBit 39 ^^ false),
  .emit [3, 5, 6, 7, 8, 12, 15, 16] (offset.testBit 40 ^^ false),
  .read 17,
  .emit [3, 6, 7, 10, 17] (offset.testBit 41 ^^ true),
  .read 18,
  .emit [0, 2, 3, 6, 10, 14, 15, 18] (offset.testBit 42 ^^ false),
  .forget 10 19,
  .emit [6, 8, 11, 12, 13, 17] (offset.testBit 43 ^^ false),
  .emit [3, 6, 8, 10, 12, 15] (offset.testBit 44 ^^ false),
  .forget 8 18,
  .read 17,
  .emit [3, 7, 8, 10, 11, 12, 14, 15, 17] (offset.testBit 45 ^^ true),
  .emit [3, 4, 6, 7, 9, 10, 14, 15, 17] (offset.testBit 46 ^^ true),
  .read 18,
  .emit [0, 2, 3, 4, 12, 18] (offset.testBit 47 ^^ false),
  .forget 12 19,
  .emit [0, 2, 4, 6, 9, 10, 12, 15] (offset.testBit 48 ^^ false),
  .forget 9 18,
  .read 17,
  .emit [0, 3, 4, 5, 6, 7, 15, 16, 17] (offset.testBit 49 ^^ true),
  .forget 4 18,
  .emit [0, 2, 3, 4, 7] (offset.testBit 50 ^^ true),
  .forget 0 17,
  .emit [2, 3, 6, 7, 10, 12, 13, 14, 15] (offset.testBit 51 ^^ true),
  .emit [3, 4, 5, 6, 13, 15] (offset.testBit 52 ^^ false),
  .forget 13 16,
  .emit [2, 3, 6, 7, 9, 10, 11, 13, 14] (offset.testBit 53 ^^ true),
  .forget 7 15,
  .read 14,
  .emit [1, 2, 6, 13, 14] (offset.testBit 54 ^^ true),
  .read 15,
  .emit [1, 2, 3, 4, 6, 13, 15] (offset.testBit 55 ^^ true),
  .read 16,
  .emit [1, 2, 3, 5, 16] (offset.testBit 56 ^^ true),
  .forget 1 17,
  .emit [3, 4, 5, 6, 11, 12, 13, 15] (offset.testBit 57 ^^ false),
  .read 16,
  .emit [0, 2, 5, 6, 7, 10, 13, 16] (offset.testBit 58 ^^ false),
  .emit [0, 1, 2, 3, 5, 6, 7, 9, 10, 13, 16] (offset.testBit 59 ^^ true),
  .emit [0, 2, 3, 4, 14, 15] (offset.testBit 60 ^^ false),
  .forget 0 17,
  .emit [3, 5, 6, 8, 10, 11, 14] (offset.testBit 61 ^^ true),
  .emit [0, 3, 5] (offset.testBit 62 ^^ true),
  .emit [0, 1, 2, 3, 5, 6] (offset.testBit 63 ^^ false),
  .forget 5 16,
  .read 15,
  .emit [6, 7, 13, 15] (offset.testBit 64 ^^ false),
  .emit [2, 7, 14, 15] (offset.testBit 65 ^^ false),
  .read 16,
  .emit [2, 3, 16] (offset.testBit 66 ^^ true),
  .forget 2 17,
  .emit [0, 1, 3, 7, 12, 14, 15] (offset.testBit 67 ^^ true),
  .emit [2, 3, 4, 5, 6, 13] (offset.testBit 68 ^^ false),
  .forget 6 16,
  .emit [3, 4, 6, 7, 8, 11, 13, 14] (offset.testBit 69 ^^ false),
  .forget 3 15,
  .emit [2, 4, 5, 12] (offset.testBit 70 ^^ false),
  .forget 12 14,
  .emit [0, 2, 4, 5, 8, 11, 12] (offset.testBit 71 ^^ true),
  .forget 8 13,
  .read 12,
  .emit [3, 8, 11, 12] (offset.testBit 72 ^^ false),
  .emit [2, 4, 5, 7, 9, 10, 11, 12] (offset.testBit 73 ^^ false),
  .emit [3, 6, 7, 11, 12] (offset.testBit 74 ^^ true),
  .forget 7 13,
  .read 12,
  .emit [8, 11, 12] (offset.testBit 75 ^^ true),
  .forget 8 13,
  .emit [2, 4, 5, 8, 11] (offset.testBit 76 ^^ true),
  .forget 2 12,
  .emit [2, 4, 7, 10] (offset.testBit 77 ^^ false),
  .emit [2, 4, 5, 8] (offset.testBit 78 ^^ false),
  .forget 4 11,
  .read 10,
  .emit [0, 5, 10] (offset.testBit 79 ^^ true),
  .forget 5 11,
  .emit [2, 3, 4, 6, 8] (offset.testBit 80 ^^ true),
  .forget 6 10,
  .emit [0, 1, 2, 4, 8] (offset.testBit 81 ^^ true),
  .forget 4 9,
  .emit [0, 3, 5] (offset.testBit 82 ^^ true),
  .forget 3 8,
  .emit [1, 5] (offset.testBit 83 ^^ false),
  .forget 1 7,
  .emit [2, 3] (offset.testBit 84 ^^ false),
  .forget 2 6,
  .emit [0, 3] (offset.testBit 85 ^^ false),
  .forget 3 5,
  .emit [0, 1, 2] (offset.testBit 86 ^^ true),
  .forget 1 4,
  .emit [1] (offset.testBit 87 ^^ true),
  .forget 1 3,
  .emit [0, 1] (offset.testBit 88 ^^ false),
  .forget 0 2,
  .emit [0] (offset.testBit 89 ^^ true),
  .forget 0 1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Structural equality of the certified and efficient numeric functions. -/
private theorem stab_raw_numeric (offset degree : Nat) : (stabRaw0 offset degree).numeric = (fun table => (stabSteps offset).foldl (fastPackedStep 42 degree) table) := by
  funext table
  rw [fastPackedFold_eq]
  simpa only [stabSteps] using congrFun (stab_numeric0 offset degree) table

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Structural equality of the certified and flattened instruction lists. -/
private theorem stab_raw_program (offset degree : Nat) : (stabRaw0 offset degree).certificate.program = stabInstructions offset := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The certified encoder sums each coefficient once. -/
private theorem stab_raw_merges (offset degree : Nat) : (stabRaw0 offset degree).merges = 41 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified encoder with a flattened implementation for efficient kernel evaluation. -/
noncomputable def stabProgram (offset degree : Nat) : PackedProgram 42 degree 0 0 :=
  PackedProgram.flatten (stabRaw0 offset degree) (stabInstructions offset)
    (fun table => (stabSteps offset).foldl (fastPackedStep 42 degree) table) 41
    (stab_raw_program offset degree) (stab_raw_numeric offset degree) (stab_raw_merges offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified generators paired with their coefficient inputs. -/
noncomputable def stabInputs : List (Nat × Nat) := [
  (957201, 1),
  (74378, 2),
  (299284, 4),
  (1553992008, 8),
  (1056298565502992, 16),
  (29792, 32),
  (3363832128, 64),
  (39256604800, 128),
  (27995228474112, 256),
  (352394583998976, 512),
  (7151120550912, 1024),
  (481137004544, 2048),
  (203815834312704, 4096),
  (17226832787915948032, 8192),
  (26311426048, 16384),
  (126100816146268160, 32768),
  (2116243010486272, 65536),
  (122060361682618417152, 131072),
  (66060288, 262144),
  (13057663642370048, 524288),
  (6764197211799552, 1048576),
  (1124944852691282034688, 2097152),
  (326203425470956961792, 4194304),
  (29128284952534787817472, 8388608),
  (45767451632189382328320, 16777216),
  (23572285054063844677124096, 33554432),
  (2018177232282845184, 67108864),
  (2953784940982230319104, 134217728),
  (3787341101463610524172288, 268435456),
  (77380697773875511146053632, 536870912),
  (1328312362507442323456, 1073741824),
  (542778336882769036050432, 2147483648),
  (6069019170517502230790144, 4294967296),
  (995535217235446783279104, 8589934592),
  (12089415641989264619601920, 17179869184),
  (433402429788787767368482816, 34359738368),
  (1228608495541277266280448, 68719476736),
  (88913306435280038789120, 137438953472),
  (58212611634334116549230592, 274877906944),
  (158784850620008950665314304, 549755813888),
  (1020937854664554338039365632, 1099511627776)]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Generators encoded by the trellis. -/
noncomputable def stabGenerators : List Nat := stabInputs.map Prod.fst

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The encoder has the required number of reads. -/
theorem stab_reads (offset : Nat) : reads (stabInstructions offset) = 41 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The encoder has the required number of outputs. -/
theorem stab_outputs (offset : Nat) : outputs (stabInstructions offset) = 90 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The encoder sums each coefficient once. -/
private theorem stab_merges (offset degree : Nat) : (stabProgram offset degree).merges = 41 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Terminal stage of the certified encoder. -/
private noncomputable def cycleRaw90 (_offset degree : Nat) : PackedProgram 50 degree 0 0 := PackedProgram.done 0

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Terminal metadata suffix. -/
private noncomputable def cycleSteps90 (_offset : Nat) : List PackedStep := []

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The terminal stage leaves its table unchanged. -/
private theorem cycle_numeric90 (offset degree : Nat) : (cycleRaw90 offset degree).numeric = (fun table => (cycleSteps90 offset).foldl (packedStep 50 degree) table) := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 89. -/
private noncomputable def cycleRaw89 (offset degree : Nat) : PackedProgram 50 degree 1 0 := PackedProgram.emit [0] (offset.testBit 89 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (cycleRaw90 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps89 (offset : Nat) : List PackedStep := (1, false, [0], 0, (offset.testBit 89 ^^ true)) :: cycleSteps90 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric89 (offset degree : Nat) :
    (cycleRaw89 offset degree).numeric =
      (fun table => (cycleSteps89 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw90 offset degree).numeric (packedStep 50 degree table (1, false, [0], 0, (offset.testBit 89 ^^ true))) = _
  rw [cycle_numeric90]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 88. -/
private noncomputable def cycleRaw88 (offset degree : Nat) : PackedProgram 50 degree 2 0 := PackedProgram.emit [0] (offset.testBit 88 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (cycleRaw89 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps88 (offset : Nat) : List PackedStep := (2, false, [0], 0, (offset.testBit 88 ^^ true)) :: cycleSteps89 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric88 (offset degree : Nat) :
    (cycleRaw88 offset degree).numeric =
      (fun table => (cycleSteps88 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw89 offset degree).numeric (packedStep 50 degree table (2, false, [0], 0, (offset.testBit 88 ^^ true))) = _
  rw [cycle_numeric89]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 87. -/
private noncomputable def cycleRaw87 (offset degree : Nat) : PackedProgram 50 degree 3 0 := PackedProgram.emit [1, 2] (offset.testBit 87 ^^ false) (by decide) (PackedProgram.forgetBitFast 1 (cycleRaw88 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps87 (offset : Nat) : List PackedStep := (3, false, [1, 2], 1, (offset.testBit 87 ^^ false)) :: cycleSteps88 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric87 (offset degree : Nat) :
    (cycleRaw87 offset degree).numeric =
      (fun table => (cycleSteps87 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw88 offset degree).numeric (packedStep 50 degree table (3, false, [1, 2], 1, (offset.testBit 87 ^^ false))) = _
  rw [cycle_numeric88]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 86. -/
private noncomputable def cycleRaw86 (offset degree : Nat) : PackedProgram 50 degree 4 0 := PackedProgram.emit [0, 2] (offset.testBit 86 ^^ false) (by decide) (PackedProgram.forgetBitFast 2 (cycleRaw87 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps86 (offset : Nat) : List PackedStep := (4, false, [0, 2], 2, (offset.testBit 86 ^^ false)) :: cycleSteps87 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric86 (offset degree : Nat) :
    (cycleRaw86 offset degree).numeric =
      (fun table => (cycleSteps86 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw87 offset degree).numeric (packedStep 50 degree table (4, false, [0, 2], 2, (offset.testBit 86 ^^ false))) = _
  rw [cycle_numeric87]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 85. -/
private noncomputable def cycleRaw85 (offset degree : Nat) : PackedProgram 50 degree 5 0 := PackedProgram.emit [0, 1, 3] (offset.testBit 85 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (cycleRaw86 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps85 (offset : Nat) : List PackedStep := (5, false, [0, 1, 3], 0, (offset.testBit 85 ^^ true)) :: cycleSteps86 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric85 (offset degree : Nat) :
    (cycleRaw85 offset degree).numeric =
      (fun table => (cycleSteps85 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw86 offset degree).numeric (packedStep 50 degree table (5, false, [0, 1, 3], 0, (offset.testBit 85 ^^ true))) = _
  rw [cycle_numeric86]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 84. -/
private noncomputable def cycleRaw84 (offset degree : Nat) : PackedProgram 50 degree 6 0 := PackedProgram.emit [0, 1, 5] (offset.testBit 84 ^^ true) (by decide) (PackedProgram.forgetBitFast 1 (cycleRaw85 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps84 (offset : Nat) : List PackedStep := (6, false, [0, 1, 5], 1, (offset.testBit 84 ^^ true)) :: cycleSteps85 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric84 (offset degree : Nat) :
    (cycleRaw84 offset degree).numeric =
      (fun table => (cycleSteps84 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw85 offset degree).numeric (packedStep 50 degree table (6, false, [0, 1, 5], 1, (offset.testBit 84 ^^ true))) = _
  rw [cycle_numeric85]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 83. -/
private noncomputable def cycleRaw83 (offset degree : Nat) : PackedProgram 50 degree 7 0 := PackedProgram.emit [0, 1, 3, 5] (offset.testBit 83 ^^ false) (by decide) (PackedProgram.forgetBitFast 3 (cycleRaw84 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps83 (offset : Nat) : List PackedStep := (7, false, [0, 1, 3, 5], 3, (offset.testBit 83 ^^ false)) :: cycleSteps84 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric83 (offset degree : Nat) :
    (cycleRaw83 offset degree).numeric =
      (fun table => (cycleSteps83 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw84 offset degree).numeric (packedStep 50 degree table (7, false, [0, 1, 3, 5], 3, (offset.testBit 83 ^^ false))) = _
  rw [cycle_numeric84]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 82. -/
private noncomputable def cycleRaw82 (offset degree : Nat) : PackedProgram 50 degree 8 0 := PackedProgram.emit [0, 1, 3, 6] (offset.testBit 82 ^^ false) (by decide) (PackedProgram.forgetBitFast 1 (cycleRaw83 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps82 (offset : Nat) : List PackedStep := (8, false, [0, 1, 3, 6], 1, (offset.testBit 82 ^^ false)) :: cycleSteps83 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric82 (offset degree : Nat) :
    (cycleRaw82 offset degree).numeric =
      (fun table => (cycleSteps82 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw83 offset degree).numeric (packedStep 50 degree table (8, false, [0, 1, 3, 6], 1, (offset.testBit 82 ^^ false))) = _
  rw [cycle_numeric83]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 81. -/
private noncomputable def cycleRaw81 (offset degree : Nat) : PackedProgram 50 degree 9 0 := PackedProgram.emit [0, 1, 2, 5, 7] (offset.testBit 81 ^^ true) (by decide) (PackedProgram.forgetBitFast 5 (cycleRaw82 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps81 (offset : Nat) : List PackedStep := (9, false, [0, 1, 2, 5, 7], 5, (offset.testBit 81 ^^ true)) :: cycleSteps82 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric81 (offset degree : Nat) :
    (cycleRaw81 offset degree).numeric =
      (fun table => (cycleSteps81 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw82 offset degree).numeric (packedStep 50 degree table (9, false, [0, 1, 2, 5, 7], 5, (offset.testBit 81 ^^ true))) = _
  rw [cycle_numeric82]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 80. -/
private noncomputable def cycleRaw80 (offset degree : Nat) : PackedProgram 50 degree 10 0 := PackedProgram.emit [2, 4, 5] (offset.testBit 80 ^^ true) (by decide) (PackedProgram.forgetBitFast 5 (cycleRaw81 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps80 (offset : Nat) : List PackedStep := (10, false, [2, 4, 5], 5, (offset.testBit 80 ^^ true)) :: cycleSteps81 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric80 (offset degree : Nat) :
    (cycleRaw80 offset degree).numeric =
      (fun table => (cycleSteps80 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw81 offset degree).numeric (packedStep 50 degree table (10, false, [2, 4, 5], 5, (offset.testBit 80 ^^ true))) = _
  rw [cycle_numeric81]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 79. -/
private noncomputable def cycleRaw79 (offset degree : Nat) : PackedProgram 50 degree 10 0 := PackedProgram.emit [1, 2, 7, 8] (offset.testBit 79 ^^ false) (by decide) (cycleRaw80 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps79 (offset : Nat) : List PackedStep := (10, false, [1, 2, 7, 8], 10, (offset.testBit 79 ^^ false)) :: cycleSteps80 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric79 (offset degree : Nat) :
    (cycleRaw79 offset degree).numeric =
      (fun table => (cycleSteps79 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw80 offset degree).numeric (packedStep 50 degree table (10, false, [1, 2, 7, 8], 10, (offset.testBit 79 ^^ false))) = _
  rw [cycle_numeric80]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 78. -/
private noncomputable def cycleRaw78 (offset degree : Nat) : PackedProgram 50 degree 11 0 := PackedProgram.emit [0, 3, 5, 7, 8, 9] (offset.testBit 78 ^^ false) (by decide) (PackedProgram.forgetBitFast 3 (cycleRaw79 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps78 (offset : Nat) : List PackedStep := (11, false, [0, 3, 5, 7, 8, 9], 3, (offset.testBit 78 ^^ false)) :: cycleSteps79 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric78 (offset degree : Nat) :
    (cycleRaw78 offset degree).numeric =
      (fun table => (cycleSteps78 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw79 offset degree).numeric (packedStep 50 degree table (11, false, [0, 3, 5, 7, 8, 9], 3, (offset.testBit 78 ^^ false))) = _
  rw [cycle_numeric79]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 77. -/
private noncomputable def cycleRaw77 (offset degree : Nat) : PackedProgram 50 degree 11 0 := PackedProgram.read (width := 11) (PackedProgram.emit [1, 3, 7, 9, 11] (offset.testBit 77 ^^ true) (by decide) (PackedProgram.forgetBitFast 7 (cycleRaw78 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps77 (offset : Nat) : List PackedStep := (12, true, [1, 3, 7, 9, 11], 7, (offset.testBit 77 ^^ true)) :: cycleSteps78 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric77 (offset degree : Nat) :
    (cycleRaw77 offset degree).numeric =
      (fun table => (cycleSteps77 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw78 offset degree).numeric (packedStep 50 degree table (12, true, [1, 3, 7, 9, 11], 7, (offset.testBit 77 ^^ true))) = _
  rw [cycle_numeric78]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 76. -/
private noncomputable def cycleRaw76 (offset degree : Nat) : PackedProgram 50 degree 12 0 := PackedProgram.emit [4, 7] (offset.testBit 76 ^^ false) (by decide) (PackedProgram.forgetBitFast 7 (cycleRaw77 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps76 (offset : Nat) : List PackedStep := (12, false, [4, 7], 7, (offset.testBit 76 ^^ false)) :: cycleSteps77 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric76 (offset degree : Nat) :
    (cycleRaw76 offset degree).numeric =
      (fun table => (cycleSteps76 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw77 offset degree).numeric (packedStep 50 degree table (12, false, [4, 7], 7, (offset.testBit 76 ^^ false))) = _
  rw [cycle_numeric77]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 75. -/
private noncomputable def cycleRaw75 (offset degree : Nat) : PackedProgram 50 degree 12 0 := PackedProgram.emit [1, 3, 6, 7] (offset.testBit 75 ^^ false) (by decide) (cycleRaw76 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps75 (offset : Nat) : List PackedStep := (12, false, [1, 3, 6, 7], 12, (offset.testBit 75 ^^ false)) :: cycleSteps76 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric75 (offset degree : Nat) :
    (cycleRaw75 offset degree).numeric =
      (fun table => (cycleSteps75 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw76 offset degree).numeric (packedStep 50 degree table (12, false, [1, 3, 6, 7], 12, (offset.testBit 75 ^^ false))) = _
  rw [cycle_numeric76]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 74. -/
private noncomputable def cycleRaw74 (offset degree : Nat) : PackedProgram 50 degree 13 0 := PackedProgram.emit [3, 4, 6, 7] (offset.testBit 74 ^^ false) (by decide) (PackedProgram.forgetBitFast 6 (cycleRaw75 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps74 (offset : Nat) : List PackedStep := (13, false, [3, 4, 6, 7], 6, (offset.testBit 74 ^^ false)) :: cycleSteps75 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric74 (offset degree : Nat) :
    (cycleRaw74 offset degree).numeric =
      (fun table => (cycleSteps74 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw75 offset degree).numeric (packedStep 50 degree table (13, false, [3, 4, 6, 7], 6, (offset.testBit 74 ^^ false))) = _
  rw [cycle_numeric75]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 73. -/
private noncomputable def cycleRaw73 (offset degree : Nat) : PackedProgram 50 degree 13 0 := PackedProgram.read (width := 13) (PackedProgram.emit [2, 4, 11, 13] (offset.testBit 73 ^^ false) (by decide) (PackedProgram.forgetBitFast 4 (cycleRaw74 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps73 (offset : Nat) : List PackedStep := (14, true, [2, 4, 11, 13], 4, (offset.testBit 73 ^^ false)) :: cycleSteps74 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric73 (offset degree : Nat) :
    (cycleRaw73 offset degree).numeric =
      (fun table => (cycleSteps73 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw74 offset degree).numeric (packedStep 50 degree table (14, true, [2, 4, 11, 13], 4, (offset.testBit 73 ^^ false))) = _
  rw [cycle_numeric74]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 72. -/
private noncomputable def cycleRaw72 (offset degree : Nat) : PackedProgram 50 degree 12 0 := PackedProgram.read (width := 12) (PackedProgram.emit [1, 2, 4, 6, 7, 9, 12] (offset.testBit 72 ^^ true) (by decide) (cycleRaw73 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps72 (offset : Nat) : List PackedStep := (13, true, [1, 2, 4, 6, 7, 9, 12], 13, (offset.testBit 72 ^^ true)) :: cycleSteps73 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric72 (offset degree : Nat) :
    (cycleRaw72 offset degree).numeric =
      (fun table => (cycleSteps72 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw73 offset degree).numeric (packedStep 50 degree table (13, true, [1, 2, 4, 6, 7, 9, 12], 13, (offset.testBit 72 ^^ true))) = _
  rw [cycle_numeric73]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 71. -/
private noncomputable def cycleRaw71 (offset degree : Nat) : PackedProgram 50 degree 13 0 := PackedProgram.emit [0, 2, 6, 8, 9, 11] (offset.testBit 71 ^^ false) (by decide) (PackedProgram.forgetBitFast 2 (cycleRaw72 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps71 (offset : Nat) : List PackedStep := (13, false, [0, 2, 6, 8, 9, 11], 2, (offset.testBit 71 ^^ false)) :: cycleSteps72 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric71 (offset degree : Nat) :
    (cycleRaw71 offset degree).numeric =
      (fun table => (cycleSteps71 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw72 offset degree).numeric (packedStep 50 degree table (13, false, [0, 2, 6, 8, 9, 11], 2, (offset.testBit 71 ^^ false))) = _
  rw [cycle_numeric72]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 70. -/
private noncomputable def cycleRaw70 (offset degree : Nat) : PackedProgram 50 degree 14 0 := PackedProgram.emit [0, 1, 2, 8, 10, 13] (offset.testBit 70 ^^ false) (by decide) (PackedProgram.forgetBitFast 10 (cycleRaw71 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps70 (offset : Nat) : List PackedStep := (14, false, [0, 1, 2, 8, 10, 13], 10, (offset.testBit 70 ^^ false)) :: cycleSteps71 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric70 (offset degree : Nat) :
    (cycleRaw70 offset degree).numeric =
      (fun table => (cycleSteps70 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw71 offset degree).numeric (packedStep 50 degree table (14, false, [0, 1, 2, 8, 10, 13], 10, (offset.testBit 70 ^^ false))) = _
  rw [cycle_numeric71]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 69. -/
private noncomputable def cycleRaw69 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.emit [3, 6, 7, 8, 9, 12] (offset.testBit 69 ^^ false) (by decide) (PackedProgram.forgetBitFast 7 (cycleRaw70 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps69 (offset : Nat) : List PackedStep := (15, false, [3, 6, 7, 8, 9, 12], 7, (offset.testBit 69 ^^ false)) :: cycleSteps70 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric69 (offset degree : Nat) :
    (cycleRaw69 offset degree).numeric =
      (fun table => (cycleSteps69 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw70 offset degree).numeric (packedStep 50 degree table (15, false, [3, 6, 7, 8, 9, 12], 7, (offset.testBit 69 ^^ false))) = _
  rw [cycle_numeric70]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 68. -/
private noncomputable def cycleRaw68 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [13, 15] (offset.testBit 68 ^^ false) (by decide) (PackedProgram.forgetBitFast 13 (cycleRaw69 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps68 (offset : Nat) : List PackedStep := (16, false, [13, 15], 13, (offset.testBit 68 ^^ false)) :: cycleSteps69 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric68 (offset degree : Nat) :
    (cycleRaw68 offset degree).numeric =
      (fun table => (cycleSteps68 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw69 offset degree).numeric (packedStep 50 degree table (16, false, [13, 15], 13, (offset.testBit 68 ^^ false))) = _
  rw [cycle_numeric69]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 67. -/
private noncomputable def cycleRaw67 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [1, 7, 8, 10, 13, 15, 16] (offset.testBit 67 ^^ true) (by decide) (PackedProgram.forgetBitFast 8 (cycleRaw68 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps67 (offset : Nat) : List PackedStep := (17, true, [1, 7, 8, 10, 13, 15, 16], 8, (offset.testBit 67 ^^ true)) :: cycleSteps68 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric67 (offset degree : Nat) :
    (cycleRaw67 offset degree).numeric =
      (fun table => (cycleSteps67 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw68 offset degree).numeric (packedStep 50 degree table (17, true, [1, 7, 8, 10, 13, 15, 16], 8, (offset.testBit 67 ^^ true))) = _
  rw [cycle_numeric68]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 66. -/
private noncomputable def cycleRaw66 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [1, 4, 6, 9, 10, 12, 13, 14] (offset.testBit 66 ^^ false) (by decide) (cycleRaw67 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps66 (offset : Nat) : List PackedStep := (16, false, [1, 4, 6, 9, 10, 12, 13, 14], 16, (offset.testBit 66 ^^ false)) :: cycleSteps67 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric66 (offset degree : Nat) :
    (cycleRaw66 offset degree).numeric =
      (fun table => (cycleSteps66 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw67 offset degree).numeric (packedStep 50 degree table (16, false, [1, 4, 6, 9, 10, 12, 13, 14], 16, (offset.testBit 66 ^^ false))) = _
  rw [cycle_numeric67]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 65. -/
private noncomputable def cycleRaw65 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [1, 3, 14, 16] (offset.testBit 65 ^^ false) (by decide) (PackedProgram.forgetBitFast 1 (cycleRaw66 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps65 (offset : Nat) : List PackedStep := (17, true, [1, 3, 14, 16], 1, (offset.testBit 65 ^^ false)) :: cycleSteps66 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric65 (offset degree : Nat) :
    (cycleRaw65 offset degree).numeric =
      (fun table => (cycleSteps65 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw66 offset degree).numeric (packedStep 50 degree table (17, true, [1, 3, 14, 16], 1, (offset.testBit 65 ^^ false))) = _
  rw [cycle_numeric66]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 64. -/
private noncomputable def cycleRaw64 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [1, 3, 5, 8, 9, 10, 13, 15] (offset.testBit 64 ^^ false) (by decide) (cycleRaw65 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps64 (offset : Nat) : List PackedStep := (16, true, [1, 3, 5, 8, 9, 10, 13, 15], 16, (offset.testBit 64 ^^ false)) :: cycleSteps65 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric64 (offset degree : Nat) :
    (cycleRaw64 offset degree).numeric =
      (fun table => (cycleSteps64 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw65 offset degree).numeric (packedStep 50 degree table (16, true, [1, 3, 5, 8, 9, 10, 13, 15], 16, (offset.testBit 64 ^^ false))) = _
  rw [cycle_numeric65]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 63. -/
private noncomputable def cycleRaw63 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [1, 3, 4, 6, 9, 10, 12, 13, 15] (offset.testBit 63 ^^ true) (by decide) (PackedProgram.forgetBitFast 3 (cycleRaw64 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps63 (offset : Nat) : List PackedStep := (16, false, [1, 3, 4, 6, 9, 10, 12, 13, 15], 3, (offset.testBit 63 ^^ true)) :: cycleSteps64 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric63 (offset degree : Nat) :
    (cycleRaw63 offset degree).numeric =
      (fun table => (cycleSteps63 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw64 offset degree).numeric (packedStep 50 degree table (16, false, [1, 3, 4, 6, 9, 10, 12, 13, 15], 3, (offset.testBit 63 ^^ true))) = _
  rw [cycle_numeric64]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 62. -/
private noncomputable def cycleRaw62 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [5, 9, 15, 16] (offset.testBit 62 ^^ false) (by decide) (PackedProgram.forgetBitFast 9 (cycleRaw63 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps62 (offset : Nat) : List PackedStep := (17, true, [5, 9, 15, 16], 9, (offset.testBit 62 ^^ false)) :: cycleSteps63 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric62 (offset degree : Nat) :
    (cycleRaw62 offset degree).numeric =
      (fun table => (cycleSteps62 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw63 offset degree).numeric (packedStep 50 degree table (17, true, [5, 9, 15, 16], 9, (offset.testBit 62 ^^ false))) = _
  rw [cycle_numeric63]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 61. -/
private noncomputable def cycleRaw61 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [0, 1, 2, 6, 9, 11, 12, 15, 16] (offset.testBit 61 ^^ true) (by decide) (PackedProgram.forgetBitFast 12 (cycleRaw62 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps61 (offset : Nat) : List PackedStep := (17, true, [0, 1, 2, 6, 9, 11, 12, 15, 16], 12, (offset.testBit 61 ^^ true)) :: cycleSteps62 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric61 (offset degree : Nat) :
    (cycleRaw61 offset degree).numeric =
      (fun table => (cycleSteps61 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw62 offset degree).numeric (packedStep 50 degree table (17, true, [0, 1, 2, 6, 9, 11, 12, 15, 16], 12, (offset.testBit 61 ^^ true))) = _
  rw [cycle_numeric62]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 60. -/
private noncomputable def cycleRaw60 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.emit [2, 4, 5, 8, 10, 11, 12, 13, 16] (offset.testBit 60 ^^ true) (by decide) (PackedProgram.forgetBitFast 5 (cycleRaw61 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps60 (offset : Nat) : List PackedStep := (17, false, [2, 4, 5, 8, 10, 11, 12, 13, 16], 5, (offset.testBit 60 ^^ true)) :: cycleSteps61 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric60 (offset degree : Nat) :
    (cycleRaw60 offset degree).numeric =
      (fun table => (cycleSteps60 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw61 offset degree).numeric (packedStep 50 degree table (17, false, [2, 4, 5, 8, 10, 11, 12, 13, 16], 5, (offset.testBit 60 ^^ true))) = _
  rw [cycle_numeric61]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 59. -/
private noncomputable def cycleRaw59 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [1, 3, 4, 5, 7, 13, 17] (offset.testBit 59 ^^ true) (by decide) (PackedProgram.forgetBitFast 4 (cycleRaw60 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps59 (offset : Nat) : List PackedStep := (18, true, [1, 3, 4, 5, 7, 13, 17], 4, (offset.testBit 59 ^^ true)) :: cycleSteps60 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric59 (offset degree : Nat) :
    (cycleRaw59 offset degree).numeric =
      (fun table => (cycleSteps59 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw60 offset degree).numeric (packedStep 50 degree table (18, true, [1, 3, 4, 5, 7, 13, 17], 4, (offset.testBit 59 ^^ true))) = _
  rw [cycle_numeric60]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 58. -/
private noncomputable def cycleRaw58 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [2, 4, 5, 8, 9, 11, 13, 16] (offset.testBit 58 ^^ false) (by decide) (cycleRaw59 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps58 (offset : Nat) : List PackedStep := (17, true, [2, 4, 5, 8, 9, 11, 13, 16], 17, (offset.testBit 58 ^^ false)) :: cycleSteps59 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric58 (offset degree : Nat) :
    (cycleRaw58 offset degree).numeric =
      (fun table => (cycleSteps58 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw59 offset degree).numeric (packedStep 50 degree table (17, true, [2, 4, 5, 8, 9, 11, 13, 16], 17, (offset.testBit 58 ^^ false))) = _
  rw [cycle_numeric59]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 57. -/
private noncomputable def cycleRaw57 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [0, 2, 4, 9, 11, 12, 16] (offset.testBit 57 ^^ true) (by decide) (PackedProgram.forgetBitFast 0 (cycleRaw58 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps57 (offset : Nat) : List PackedStep := (17, true, [0, 2, 4, 9, 11, 12, 16], 0, (offset.testBit 57 ^^ true)) :: cycleSteps58 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric57 (offset degree : Nat) :
    (cycleRaw57 offset degree).numeric =
      (fun table => (cycleSteps57 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw58 offset degree).numeric (packedStep 50 degree table (17, true, [0, 2, 4, 9, 11, 12, 16], 0, (offset.testBit 57 ^^ true))) = _
  rw [cycle_numeric58]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 56. -/
private noncomputable def cycleRaw56 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [4, 5, 6, 8, 13, 15] (offset.testBit 56 ^^ false) (by decide) (cycleRaw57 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps56 (offset : Nat) : List PackedStep := (16, false, [4, 5, 6, 8, 13, 15], 16, (offset.testBit 56 ^^ false)) :: cycleSteps57 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric56 (offset degree : Nat) :
    (cycleRaw56 offset degree).numeric =
      (fun table => (cycleSteps56 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw57 offset degree).numeric (packedStep 50 degree table (16, false, [4, 5, 6, 8, 13, 15], 16, (offset.testBit 56 ^^ false))) = _
  rw [cycle_numeric57]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 55. -/
private noncomputable def cycleRaw55 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [0, 4, 5, 6, 8, 9, 14, 15] (offset.testBit 55 ^^ false) (by decide) (cycleRaw56 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps55 (offset : Nat) : List PackedStep := (16, true, [0, 4, 5, 6, 8, 9, 14, 15], 16, (offset.testBit 55 ^^ false)) :: cycleSteps56 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric55 (offset degree : Nat) :
    (cycleRaw55 offset degree).numeric =
      (fun table => (cycleSteps55 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw56 offset degree).numeric (packedStep 50 degree table (16, true, [0, 4, 5, 6, 8, 9, 14, 15], 16, (offset.testBit 55 ^^ false))) = _
  rw [cycle_numeric56]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 54. -/
private noncomputable def cycleRaw54 (offset degree : Nat) : PackedProgram 50 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [5, 9, 14] (offset.testBit 54 ^^ true) (by decide) (cycleRaw55 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps54 (offset : Nat) : List PackedStep := (15, true, [5, 9, 14], 15, (offset.testBit 54 ^^ true)) :: cycleSteps55 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric54 (offset degree : Nat) :
    (cycleRaw54 offset degree).numeric =
      (fun table => (cycleSteps54 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw55 offset degree).numeric (packedStep 50 degree table (15, true, [5, 9, 14], 15, (offset.testBit 54 ^^ true))) = _
  rw [cycle_numeric55]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 53. -/
private noncomputable def cycleRaw53 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.emit [0, 1, 2, 3, 5, 7, 9, 11, 12] (offset.testBit 53 ^^ true) (by decide) (PackedProgram.forgetBitFast 7 (cycleRaw54 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps53 (offset : Nat) : List PackedStep := (15, false, [0, 1, 2, 3, 5, 7, 9, 11, 12], 7, (offset.testBit 53 ^^ true)) :: cycleSteps54 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric53 (offset degree : Nat) :
    (cycleRaw53 offset degree).numeric =
      (fun table => (cycleSteps53 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw54 offset degree).numeric (packedStep 50 degree table (15, false, [0, 1, 2, 3, 5, 7, 9, 11, 12], 7, (offset.testBit 53 ^^ true))) = _
  rw [cycle_numeric54]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 52. -/
private noncomputable def cycleRaw52 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [1, 2, 3, 5, 6, 9, 11, 12, 13, 15] (offset.testBit 52 ^^ false) (by decide) (PackedProgram.forgetBitFast 15 (cycleRaw53 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps52 (offset : Nat) : List PackedStep := (16, false, [1, 2, 3, 5, 6, 9, 11, 12, 13, 15], 15, (offset.testBit 52 ^^ false)) :: cycleSteps53 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric52 (offset degree : Nat) :
    (cycleRaw52 offset degree).numeric =
      (fun table => (cycleSteps52 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw53 offset degree).numeric (packedStep 50 degree table (16, false, [1, 2, 3, 5, 6, 9, 11, 12, 13, 15], 15, (offset.testBit 52 ^^ false))) = _
  rw [cycle_numeric53]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 51. -/
private noncomputable def cycleRaw51 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [2, 7, 11, 13, 15, 16] (offset.testBit 51 ^^ false) (by decide) (PackedProgram.forgetBitFast 11 (cycleRaw52 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps51 (offset : Nat) : List PackedStep := (17, true, [2, 7, 11, 13, 15, 16], 11, (offset.testBit 51 ^^ false)) :: cycleSteps52 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric51 (offset degree : Nat) :
    (cycleRaw51 offset degree).numeric =
      (fun table => (cycleSteps51 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw52 offset degree).numeric (packedStep 50 degree table (17, true, [2, 7, 11, 13, 15, 16], 11, (offset.testBit 51 ^^ false))) = _
  rw [cycle_numeric52]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 50. -/
private noncomputable def cycleRaw50 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.emit [2, 5, 10, 12, 15, 16] (offset.testBit 50 ^^ false) (by decide) (PackedProgram.forgetBitFast 15 (cycleRaw51 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps50 (offset : Nat) : List PackedStep := (17, false, [2, 5, 10, 12, 15, 16], 15, (offset.testBit 50 ^^ false)) :: cycleSteps51 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric50 (offset degree : Nat) :
    (cycleRaw50 offset degree).numeric =
      (fun table => (cycleSteps50 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw51 offset degree).numeric (packedStep 50 degree table (17, false, [2, 5, 10, 12, 15, 16], 15, (offset.testBit 50 ^^ false))) = _
  rw [cycle_numeric51]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 49. -/
private noncomputable def cycleRaw49 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.emit [1, 3, 9, 10, 13, 14, 15] (offset.testBit 49 ^^ true) (by decide) (cycleRaw50 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps49 (offset : Nat) : List PackedStep := (17, false, [1, 3, 9, 10, 13, 14, 15], 17, (offset.testBit 49 ^^ true)) :: cycleSteps50 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric49 (offset degree : Nat) :
    (cycleRaw49 offset degree).numeric =
      (fun table => (cycleSteps49 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw50 offset degree).numeric (packedStep 50 degree table (17, false, [1, 3, 9, 10, 13, 14, 15], 17, (offset.testBit 49 ^^ true))) = _
  rw [cycle_numeric50]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 48. -/
private noncomputable def cycleRaw48 (offset degree : Nat) : PackedProgram 50 degree 18 0 := PackedProgram.emit [0, 1, 2, 7, 9, 12, 13, 14, 16] (offset.testBit 48 ^^ true) (by decide) (PackedProgram.forgetBitFast 14 (cycleRaw49 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps48 (offset : Nat) : List PackedStep := (18, false, [0, 1, 2, 7, 9, 12, 13, 14, 16], 14, (offset.testBit 48 ^^ true)) :: cycleSteps49 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric48 (offset degree : Nat) :
    (cycleRaw48 offset degree).numeric =
      (fun table => (cycleSteps48 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw49 offset degree).numeric (packedStep 50 degree table (18, false, [0, 1, 2, 7, 9, 12, 13, 14, 16], 14, (offset.testBit 48 ^^ true))) = _
  rw [cycle_numeric49]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 47. -/
private noncomputable def cycleRaw47 (offset degree : Nat) : PackedProgram 50 degree 18 0 := PackedProgram.emit [1, 4, 8, 11, 13, 14, 17] (offset.testBit 47 ^^ true) (by decide) (cycleRaw48 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps47 (offset : Nat) : List PackedStep := (18, false, [1, 4, 8, 11, 13, 14, 17], 18, (offset.testBit 47 ^^ true)) :: cycleSteps48 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric47 (offset degree : Nat) :
    (cycleRaw47 offset degree).numeric =
      (fun table => (cycleSteps47 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw48 offset degree).numeric (packedStep 50 degree table (18, false, [1, 4, 8, 11, 13, 14, 17], 18, (offset.testBit 47 ^^ true))) = _
  rw [cycle_numeric48]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 46. -/
private noncomputable def cycleRaw46 (offset degree : Nat) : PackedProgram 50 degree 18 0 := PackedProgram.read (width := 18) (PackedProgram.emit [1, 2, 4, 5, 7, 12, 14, 15, 18] (offset.testBit 46 ^^ true) (by decide) (PackedProgram.forgetBitFast 2 (cycleRaw47 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps46 (offset : Nat) : List PackedStep := (19, true, [1, 2, 4, 5, 7, 12, 14, 15, 18], 2, (offset.testBit 46 ^^ true)) :: cycleSteps47 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric46 (offset degree : Nat) :
    (cycleRaw46 offset degree).numeric =
      (fun table => (cycleSteps46 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw47 offset degree).numeric (packedStep 50 degree table (19, true, [1, 2, 4, 5, 7, 12, 14, 15, 18], 2, (offset.testBit 46 ^^ true))) = _
  rw [cycle_numeric47]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 45. -/
private noncomputable def cycleRaw45 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [0, 1, 2, 5, 9, 13, 14, 15, 17] (offset.testBit 45 ^^ true) (by decide) (cycleRaw46 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps45 (offset : Nat) : List PackedStep := (18, true, [0, 1, 2, 5, 9, 13, 14, 15, 17], 18, (offset.testBit 45 ^^ true)) :: cycleSteps46 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric45 (offset degree : Nat) :
    (cycleRaw45 offset degree).numeric =
      (fun table => (cycleSteps45 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw46 offset degree).numeric (packedStep 50 degree table (18, true, [0, 1, 2, 5, 9, 13, 14, 15, 17], 18, (offset.testBit 45 ^^ true))) = _
  rw [cycle_numeric46]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 44. -/
private noncomputable def cycleRaw44 (offset degree : Nat) : PackedProgram 50 degree 18 0 := PackedProgram.emit [0, 6, 7, 13, 16, 17] (offset.testBit 44 ^^ false) (by decide) (PackedProgram.forgetBitFast 7 (cycleRaw45 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps44 (offset : Nat) : List PackedStep := (18, false, [0, 6, 7, 13, 16, 17], 7, (offset.testBit 44 ^^ false)) :: cycleSteps45 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric44 (offset degree : Nat) :
    (cycleRaw44 offset degree).numeric =
      (fun table => (cycleSteps44 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw45 offset degree).numeric (packedStep 50 degree table (18, false, [0, 6, 7, 13, 16, 17], 7, (offset.testBit 44 ^^ false))) = _
  rw [cycle_numeric45]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 43. -/
private noncomputable def cycleRaw43 (offset degree : Nat) : PackedProgram 50 degree 18 0 := PackedProgram.read (width := 18) (PackedProgram.emit [0, 5, 6, 7, 12, 13, 17, 18] (offset.testBit 43 ^^ false) (by decide) (PackedProgram.forgetBitFast 6 (cycleRaw44 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps43 (offset : Nat) : List PackedStep := (19, true, [0, 5, 6, 7, 12, 13, 17, 18], 6, (offset.testBit 43 ^^ false)) :: cycleSteps44 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric43 (offset degree : Nat) :
    (cycleRaw43 offset degree).numeric =
      (fun table => (cycleSteps43 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw44 offset degree).numeric (packedStep 50 degree table (19, true, [0, 5, 6, 7, 12, 13, 17, 18], 6, (offset.testBit 43 ^^ false))) = _
  rw [cycle_numeric44]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 42. -/
private noncomputable def cycleRaw42 (offset degree : Nat) : PackedProgram 50 degree 18 0 := PackedProgram.emit [4, 5, 7, 8, 9, 11, 14, 16, 17] (offset.testBit 42 ^^ true) (by decide) (cycleRaw43 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps42 (offset : Nat) : List PackedStep := (18, false, [4, 5, 7, 8, 9, 11, 14, 16, 17], 18, (offset.testBit 42 ^^ true)) :: cycleSteps43 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric42 (offset degree : Nat) :
    (cycleRaw42 offset degree).numeric =
      (fun table => (cycleSteps42 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw43 offset degree).numeric (packedStep 50 degree table (18, false, [4, 5, 7, 8, 9, 11, 14, 16, 17], 18, (offset.testBit 42 ^^ true))) = _
  rw [cycle_numeric43]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 41. -/
private noncomputable def cycleRaw41 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [2, 6, 7, 14, 15, 17] (offset.testBit 41 ^^ false) (by decide) (cycleRaw42 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps41 (offset : Nat) : List PackedStep := (18, true, [2, 6, 7, 14, 15, 17], 18, (offset.testBit 41 ^^ false)) :: cycleSteps42 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric41 (offset degree : Nat) :
    (cycleRaw41 offset degree).numeric =
      (fun table => (cycleSteps41 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw42 offset degree).numeric (packedStep 50 degree table (18, true, [2, 6, 7, 14, 15, 17], 18, (offset.testBit 41 ^^ false))) = _
  rw [cycle_numeric42]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 40. -/
private noncomputable def cycleRaw40 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [5, 6, 12, 16, 17] (offset.testBit 40 ^^ true) (by decide) (PackedProgram.forgetBitFast 12 (cycleRaw41 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps40 (offset : Nat) : List PackedStep := (18, true, [5, 6, 12, 16, 17], 12, (offset.testBit 40 ^^ true)) :: cycleSteps41 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric40 (offset degree : Nat) :
    (cycleRaw40 offset degree).numeric =
      (fun table => (cycleSteps40 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw41 offset degree).numeric (packedStep 50 degree table (18, true, [5, 6, 12, 16, 17], 12, (offset.testBit 40 ^^ true))) = _
  rw [cycle_numeric41]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 39. -/
private noncomputable def cycleRaw39 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [6, 12, 15, 16] (offset.testBit 39 ^^ false) (by decide) (cycleRaw40 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps39 (offset : Nat) : List PackedStep := (17, true, [6, 12, 15, 16], 17, (offset.testBit 39 ^^ false)) :: cycleSteps40 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric39 (offset degree : Nat) :
    (cycleRaw39 offset degree).numeric =
      (fun table => (cycleSteps39 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw40 offset degree).numeric (packedStep 50 degree table (17, true, [6, 12, 15, 16], 17, (offset.testBit 39 ^^ false))) = _
  rw [cycle_numeric40]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 38. -/
private noncomputable def cycleRaw38 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [1, 2, 3, 4, 5, 6, 7, 14, 15] (offset.testBit 38 ^^ true) (by decide) (cycleRaw39 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps38 (offset : Nat) : List PackedStep := (16, false, [1, 2, 3, 4, 5, 6, 7, 14, 15], 16, (offset.testBit 38 ^^ true)) :: cycleSteps39 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric38 (offset degree : Nat) :
    (cycleRaw38 offset degree).numeric =
      (fun table => (cycleSteps38 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw39 offset degree).numeric (packedStep 50 degree table (16, false, [1, 2, 3, 4, 5, 6, 7, 14, 15], 16, (offset.testBit 38 ^^ true))) = _
  rw [cycle_numeric39]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 37. -/
private noncomputable def cycleRaw37 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [6, 12, 15] (offset.testBit 37 ^^ true) (by decide) (cycleRaw38 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps37 (offset : Nat) : List PackedStep := (16, true, [6, 12, 15], 16, (offset.testBit 37 ^^ true)) :: cycleSteps38 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric37 (offset degree : Nat) :
    (cycleRaw37 offset degree).numeric =
      (fun table => (cycleSteps37 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw38 offset degree).numeric (packedStep 50 degree table (16, true, [6, 12, 15], 16, (offset.testBit 37 ^^ true))) = _
  rw [cycle_numeric38]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 36. -/
private noncomputable def cycleRaw36 (offset degree : Nat) : PackedProgram 50 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [7, 14] (offset.testBit 36 ^^ false) (by decide) (cycleRaw37 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps36 (offset : Nat) : List PackedStep := (15, true, [7, 14], 15, (offset.testBit 36 ^^ false)) :: cycleSteps37 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric36 (offset degree : Nat) :
    (cycleRaw36 offset degree).numeric =
      (fun table => (cycleSteps36 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw37 offset degree).numeric (packedStep 50 degree table (15, true, [7, 14], 15, (offset.testBit 36 ^^ false))) = _
  rw [cycle_numeric37]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 35. -/
private noncomputable def cycleRaw35 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.emit [0, 2, 4, 5, 7, 8, 9, 12] (offset.testBit 35 ^^ false) (by decide) (PackedProgram.forgetBitFast 12 (cycleRaw36 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps35 (offset : Nat) : List PackedStep := (15, false, [0, 2, 4, 5, 7, 8, 9, 12], 12, (offset.testBit 35 ^^ false)) :: cycleSteps36 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric35 (offset degree : Nat) :
    (cycleRaw35 offset degree).numeric =
      (fun table => (cycleSteps35 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw36 offset degree).numeric (packedStep 50 degree table (15, false, [0, 2, 4, 5, 7, 8, 9, 12], 12, (offset.testBit 35 ^^ false))) = _
  rw [cycle_numeric36]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 34. -/
private noncomputable def cycleRaw34 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [1, 2, 4, 5, 7, 8, 9, 10, 11] (offset.testBit 34 ^^ true) (by decide) (PackedProgram.forgetBitFast 4 (cycleRaw35 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps34 (offset : Nat) : List PackedStep := (16, false, [1, 2, 4, 5, 7, 8, 9, 10, 11], 4, (offset.testBit 34 ^^ true)) :: cycleSteps35 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric34 (offset degree : Nat) :
    (cycleRaw34 offset degree).numeric =
      (fun table => (cycleSteps34 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw35 offset degree).numeric (packedStep 50 degree table (16, false, [1, 2, 4, 5, 7, 8, 9, 10, 11], 4, (offset.testBit 34 ^^ true))) = _
  rw [cycle_numeric35]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 33. -/
private noncomputable def cycleRaw33 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [1, 2, 7, 8, 9, 10, 16] (offset.testBit 33 ^^ true) (by decide) (PackedProgram.forgetBitFast 10 (cycleRaw34 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps33 (offset : Nat) : List PackedStep := (17, true, [1, 2, 7, 8, 9, 10, 16], 10, (offset.testBit 33 ^^ true)) :: cycleSteps34 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric33 (offset degree : Nat) :
    (cycleRaw33 offset degree).numeric =
      (fun table => (cycleSteps33 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw34 offset degree).numeric (packedStep 50 degree table (17, true, [1, 2, 7, 8, 9, 10, 16], 10, (offset.testBit 33 ^^ true))) = _
  rw [cycle_numeric34]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 32. -/
private noncomputable def cycleRaw32 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [0, 2, 5, 6, 8, 9, 11, 14, 15, 16] (offset.testBit 32 ^^ false) (by decide) (PackedProgram.forgetBitFast 8 (cycleRaw33 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps32 (offset : Nat) : List PackedStep := (17, true, [0, 2, 5, 6, 8, 9, 11, 14, 15, 16], 8, (offset.testBit 32 ^^ false)) :: cycleSteps33 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric32 (offset degree : Nat) :
    (cycleRaw32 offset degree).numeric =
      (fun table => (cycleSteps32 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw33 offset degree).numeric (packedStep 50 degree table (17, true, [0, 2, 5, 6, 8, 9, 11, 14, 15, 16], 8, (offset.testBit 32 ^^ false))) = _
  rw [cycle_numeric33]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 31. -/
private noncomputable def cycleRaw31 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [0, 3, 5, 10, 12, 13, 15] (offset.testBit 31 ^^ true) (by decide) (cycleRaw32 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps31 (offset : Nat) : List PackedStep := (16, false, [0, 3, 5, 10, 12, 13, 15], 16, (offset.testBit 31 ^^ true)) :: cycleSteps32 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric31 (offset degree : Nat) :
    (cycleRaw31 offset degree).numeric =
      (fun table => (cycleSteps31 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw32 offset degree).numeric (packedStep 50 degree table (16, false, [0, 3, 5, 10, 12, 13, 15], 16, (offset.testBit 31 ^^ true))) = _
  rw [cycle_numeric32]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 30. -/
private noncomputable def cycleRaw30 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.emit [1, 3, 4, 8, 9, 10, 13, 15, 16] (offset.testBit 30 ^^ true) (by decide) (PackedProgram.forgetBitFast 9 (cycleRaw31 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps30 (offset : Nat) : List PackedStep := (17, false, [1, 3, 4, 8, 9, 10, 13, 15, 16], 9, (offset.testBit 30 ^^ true)) :: cycleSteps31 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric30 (offset degree : Nat) :
    (cycleRaw30 offset degree).numeric =
      (fun table => (cycleSteps30 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw31 offset degree).numeric (packedStep 50 degree table (17, false, [1, 3, 4, 8, 9, 10, 13, 15, 16], 9, (offset.testBit 30 ^^ true))) = _
  rw [cycle_numeric31]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 29. -/
private noncomputable def cycleRaw29 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [7, 9, 11, 17] (offset.testBit 29 ^^ false) (by decide) (PackedProgram.forgetBitFast 11 (cycleRaw30 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps29 (offset : Nat) : List PackedStep := (18, true, [7, 9, 11, 17], 11, (offset.testBit 29 ^^ false)) :: cycleSteps30 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric29 (offset degree : Nat) :
    (cycleRaw29 offset degree).numeric =
      (fun table => (cycleSteps29 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw30 offset degree).numeric (packedStep 50 degree table (18, true, [7, 9, 11, 17], 11, (offset.testBit 29 ^^ false))) = _
  rw [cycle_numeric30]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 28. -/
private noncomputable def cycleRaw28 (offset degree : Nat) : PackedProgram 50 degree 17 0 := PackedProgram.read (width := 17) (PackedProgram.emit [0, 5, 9, 10, 12, 13, 17] (offset.testBit 28 ^^ true) (by decide) (PackedProgram.forgetBitFast 13 (cycleRaw29 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps28 (offset : Nat) : List PackedStep := (18, true, [0, 5, 9, 10, 12, 13, 17], 13, (offset.testBit 28 ^^ true)) :: cycleSteps29 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric28 (offset degree : Nat) :
    (cycleRaw28 offset degree).numeric =
      (fun table => (cycleSteps28 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw29 offset degree).numeric (packedStep 50 degree table (18, true, [0, 5, 9, 10, 12, 13, 17], 13, (offset.testBit 28 ^^ true))) = _
  rw [cycle_numeric29]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 27. -/
private noncomputable def cycleRaw27 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.read (width := 16) (PackedProgram.emit [4, 8, 11, 13, 16] (offset.testBit 27 ^^ true) (by decide) (cycleRaw28 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps27 (offset : Nat) : List PackedStep := (17, true, [4, 8, 11, 13, 16], 17, (offset.testBit 27 ^^ true)) :: cycleSteps28 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric27 (offset degree : Nat) :
    (cycleRaw27 offset degree).numeric =
      (fun table => (cycleSteps27 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw28 offset degree).numeric (packedStep 50 degree table (17, true, [4, 8, 11, 13, 16], 17, (offset.testBit 27 ^^ true))) = _
  rw [cycle_numeric28]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 26. -/
private noncomputable def cycleRaw26 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [0, 4, 6, 8, 10, 11, 15] (offset.testBit 26 ^^ true) (by decide) (cycleRaw27 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps26 (offset : Nat) : List PackedStep := (16, true, [0, 4, 6, 8, 10, 11, 15], 16, (offset.testBit 26 ^^ true)) :: cycleSteps27 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric26 (offset degree : Nat) :
    (cycleRaw26 offset degree).numeric =
      (fun table => (cycleSteps26 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw27 offset degree).numeric (packedStep 50 degree table (16, true, [0, 4, 6, 8, 10, 11, 15], 16, (offset.testBit 26 ^^ true))) = _
  rw [cycle_numeric27]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 25. -/
private noncomputable def cycleRaw25 (offset degree : Nat) : PackedProgram 50 degree 16 0 := PackedProgram.emit [0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 15] (offset.testBit 25 ^^ true) (by decide) (PackedProgram.forgetBitFast 2 (cycleRaw26 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps25 (offset : Nat) : List PackedStep := (16, false, [0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 15], 2, (offset.testBit 25 ^^ true)) :: cycleSteps26 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric25 (offset degree : Nat) :
    (cycleRaw25 offset degree).numeric =
      (fun table => (cycleSteps25 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw26 offset degree).numeric (packedStep 50 degree table (16, false, [0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 15], 2, (offset.testBit 25 ^^ true))) = _
  rw [cycle_numeric26]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 24. -/
private noncomputable def cycleRaw24 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [2, 7, 12, 15] (offset.testBit 24 ^^ false) (by decide) (cycleRaw25 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps24 (offset : Nat) : List PackedStep := (16, true, [2, 7, 12, 15], 16, (offset.testBit 24 ^^ false)) :: cycleSteps25 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric24 (offset degree : Nat) :
    (cycleRaw24 offset degree).numeric =
      (fun table => (cycleSteps24 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw25 offset degree).numeric (packedStep 50 degree table (16, true, [2, 7, 12, 15], 16, (offset.testBit 24 ^^ false))) = _
  rw [cycle_numeric25]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 23. -/
private noncomputable def cycleRaw23 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [0, 1, 4, 5, 6, 8, 9, 11, 12, 13, 15] (offset.testBit 23 ^^ true) (by decide) (PackedProgram.forgetBitFast 1 (cycleRaw24 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps23 (offset : Nat) : List PackedStep := (16, true, [0, 1, 4, 5, 6, 8, 9, 11, 12, 13, 15], 1, (offset.testBit 23 ^^ true)) :: cycleSteps24 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric23 (offset degree : Nat) :
    (cycleRaw23 offset degree).numeric =
      (fun table => (cycleSteps23 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw24 offset degree).numeric (packedStep 50 degree table (16, true, [0, 1, 4, 5, 6, 8, 9, 11, 12, 13, 15], 1, (offset.testBit 23 ^^ true))) = _
  rw [cycle_numeric24]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 22. -/
private noncomputable def cycleRaw22 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [1, 7, 8, 9, 10, 15] (offset.testBit 22 ^^ false) (by decide) (PackedProgram.forgetBitFast 7 (cycleRaw23 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps22 (offset : Nat) : List PackedStep := (16, true, [1, 7, 8, 9, 10, 15], 7, (offset.testBit 22 ^^ false)) :: cycleSteps23 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric22 (offset degree : Nat) :
    (cycleRaw22 offset degree).numeric =
      (fun table => (cycleSteps22 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw23 offset degree).numeric (packedStep 50 degree table (16, true, [1, 7, 8, 9, 10, 15], 7, (offset.testBit 22 ^^ false))) = _
  rw [cycle_numeric23]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 21. -/
private noncomputable def cycleRaw21 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.read (width := 15) (PackedProgram.emit [3, 4, 7, 8, 11, 13, 15] (offset.testBit 21 ^^ true) (by decide) (PackedProgram.forgetBitFast 3 (cycleRaw22 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps21 (offset : Nat) : List PackedStep := (16, true, [3, 4, 7, 8, 11, 13, 15], 3, (offset.testBit 21 ^^ true)) :: cycleSteps22 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric21 (offset degree : Nat) :
    (cycleRaw21 offset degree).numeric =
      (fun table => (cycleSteps21 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw22 offset degree).numeric (packedStep 50 degree table (16, true, [3, 4, 7, 8, 11, 13, 15], 3, (offset.testBit 21 ^^ true))) = _
  rw [cycle_numeric22]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 20. -/
private noncomputable def cycleRaw20 (offset degree : Nat) : PackedProgram 50 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [3, 4, 14] (offset.testBit 20 ^^ true) (by decide) (cycleRaw21 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps20 (offset : Nat) : List PackedStep := (15, true, [3, 4, 14], 15, (offset.testBit 20 ^^ true)) :: cycleSteps21 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric20 (offset degree : Nat) :
    (cycleRaw20 offset degree).numeric =
      (fun table => (cycleSteps20 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw21 offset degree).numeric (packedStep 50 degree table (15, true, [3, 4, 14], 15, (offset.testBit 20 ^^ true))) = _
  rw [cycle_numeric21]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 19. -/
private noncomputable def cycleRaw19 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.emit [4, 5, 8, 11, 13, 14] (offset.testBit 19 ^^ false) (by decide) (PackedProgram.forgetBitFast 5 (cycleRaw20 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps19 (offset : Nat) : List PackedStep := (15, false, [4, 5, 8, 11, 13, 14], 5, (offset.testBit 19 ^^ false)) :: cycleSteps20 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric19 (offset degree : Nat) :
    (cycleRaw19 offset degree).numeric =
      (fun table => (cycleSteps19 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw20 offset degree).numeric (packedStep 50 degree table (15, false, [4, 5, 8, 11, 13, 14], 5, (offset.testBit 19 ^^ false))) = _
  rw [cycle_numeric20]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 18. -/
private noncomputable def cycleRaw18 (offset degree : Nat) : PackedProgram 50 degree 15 0 := PackedProgram.emit [3, 4, 5, 7, 8, 11, 13] (offset.testBit 18 ^^ true) (by decide) (cycleRaw19 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps18 (offset : Nat) : List PackedStep := (15, false, [3, 4, 5, 7, 8, 11, 13], 15, (offset.testBit 18 ^^ true)) :: cycleSteps19 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric18 (offset degree : Nat) :
    (cycleRaw18 offset degree).numeric =
      (fun table => (cycleSteps18 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw19 offset degree).numeric (packedStep 50 degree table (15, false, [3, 4, 5, 7, 8, 11, 13], 15, (offset.testBit 18 ^^ true))) = _
  rw [cycle_numeric19]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 17. -/
private noncomputable def cycleRaw17 (offset degree : Nat) : PackedProgram 50 degree 14 0 := PackedProgram.read (width := 14) (PackedProgram.emit [0, 4, 5, 6, 7, 8, 10, 11, 13, 14] (offset.testBit 17 ^^ false) (by decide) (cycleRaw18 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps17 (offset : Nat) : List PackedStep := (15, true, [0, 4, 5, 6, 7, 8, 10, 11, 13, 14], 15, (offset.testBit 17 ^^ false)) :: cycleSteps18 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric17 (offset degree : Nat) :
    (cycleRaw17 offset degree).numeric =
      (fun table => (cycleSteps17 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw18 offset degree).numeric (packedStep 50 degree table (15, true, [0, 4, 5, 6, 7, 8, 10, 11, 13, 14], 15, (offset.testBit 17 ^^ false))) = _
  rw [cycle_numeric18]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 16. -/
private noncomputable def cycleRaw16 (offset degree : Nat) : PackedProgram 50 degree 14 0 := PackedProgram.emit [1, 5, 7, 9, 10, 12] (offset.testBit 16 ^^ false) (by decide) (cycleRaw17 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps16 (offset : Nat) : List PackedStep := (14, false, [1, 5, 7, 9, 10, 12], 14, (offset.testBit 16 ^^ false)) :: cycleSteps17 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric16 (offset degree : Nat) :
    (cycleRaw16 offset degree).numeric =
      (fun table => (cycleSteps16 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw17 offset degree).numeric (packedStep 50 degree table (14, false, [1, 5, 7, 9, 10, 12], 14, (offset.testBit 16 ^^ false))) = _
  rw [cycle_numeric17]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 15. -/
private noncomputable def cycleRaw15 (offset degree : Nat) : PackedProgram 50 degree 13 0 := PackedProgram.read (width := 13) (PackedProgram.emit [1, 5, 7, 13] (offset.testBit 15 ^^ false) (by decide) (cycleRaw16 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps15 (offset : Nat) : List PackedStep := (14, true, [1, 5, 7, 13], 14, (offset.testBit 15 ^^ false)) :: cycleSteps16 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric15 (offset degree : Nat) :
    (cycleRaw15 offset degree).numeric =
      (fun table => (cycleSteps15 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw16 offset degree).numeric (packedStep 50 degree table (14, true, [1, 5, 7, 13], 14, (offset.testBit 15 ^^ false))) = _
  rw [cycle_numeric16]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 14. -/
private noncomputable def cycleRaw14 (offset degree : Nat) : PackedProgram 50 degree 13 0 := PackedProgram.emit [4, 5, 6, 7, 8, 9, 11, 12] (offset.testBit 14 ^^ false) (by decide) (cycleRaw15 offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps14 (offset : Nat) : List PackedStep := (13, false, [4, 5, 6, 7, 8, 9, 11, 12], 13, (offset.testBit 14 ^^ false)) :: cycleSteps15 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric14 (offset degree : Nat) :
    (cycleRaw14 offset degree).numeric =
      (fun table => (cycleSteps14 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw15 offset degree).numeric (packedStep 50 degree table (13, false, [4, 5, 6, 7, 8, 9, 11, 12], 13, (offset.testBit 14 ^^ false))) = _
  rw [cycle_numeric15]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 13. -/
private noncomputable def cycleRaw13 (offset degree : Nat) : PackedProgram 50 degree 12 0 := PackedProgram.read (width := 12) (PackedProgram.emit [2, 10, 12] (offset.testBit 13 ^^ true) (by decide) (cycleRaw14 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps13 (offset : Nat) : List PackedStep := (13, true, [2, 10, 12], 13, (offset.testBit 13 ^^ true)) :: cycleSteps14 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric13 (offset degree : Nat) :
    (cycleRaw13 offset degree).numeric =
      (fun table => (cycleSteps13 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw14 offset degree).numeric (packedStep 50 degree table (13, true, [2, 10, 12], 13, (offset.testBit 13 ^^ true))) = _
  rw [cycle_numeric14]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 12. -/
private noncomputable def cycleRaw12 (offset degree : Nat) : PackedProgram 50 degree 11 0 := PackedProgram.read (width := 11) (PackedProgram.emit [2, 11] (offset.testBit 12 ^^ false) (by decide) (cycleRaw13 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps12 (offset : Nat) : List PackedStep := (12, true, [2, 11], 12, (offset.testBit 12 ^^ false)) :: cycleSteps13 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric12 (offset degree : Nat) :
    (cycleRaw12 offset degree).numeric =
      (fun table => (cycleSteps12 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw13 offset degree).numeric (packedStep 50 degree table (12, true, [2, 11], 12, (offset.testBit 12 ^^ false))) = _
  rw [cycle_numeric13]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 11. -/
private noncomputable def cycleRaw11 (offset degree : Nat) : PackedProgram 50 degree 11 0 := PackedProgram.read (width := 11) (PackedProgram.emit [0, 6, 7, 9, 10, 11] (offset.testBit 11 ^^ false) (by decide) (PackedProgram.forgetBitFast 0 (cycleRaw12 offset degree)))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps11 (offset : Nat) : List PackedStep := (12, true, [0, 6, 7, 9, 10, 11], 0, (offset.testBit 11 ^^ false)) :: cycleSteps12 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric11 (offset degree : Nat) :
    (cycleRaw11 offset degree).numeric =
      (fun table => (cycleSteps11 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw12 offset degree).numeric (packedStep 50 degree table (12, true, [0, 6, 7, 9, 10, 11], 0, (offset.testBit 11 ^^ false))) = _
  rw [cycle_numeric12]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 10. -/
private noncomputable def cycleRaw10 (offset degree : Nat) : PackedProgram 50 degree 10 0 := PackedProgram.read (width := 10) (PackedProgram.emit [0, 7, 8, 9, 10] (offset.testBit 10 ^^ true) (by decide) (cycleRaw11 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps10 (offset : Nat) : List PackedStep := (11, true, [0, 7, 8, 9, 10], 11, (offset.testBit 10 ^^ true)) :: cycleSteps11 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric10 (offset degree : Nat) :
    (cycleRaw10 offset degree).numeric =
      (fun table => (cycleSteps10 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw11 offset degree).numeric (packedStep 50 degree table (11, true, [0, 7, 8, 9, 10], 11, (offset.testBit 10 ^^ true))) = _
  rw [cycle_numeric11]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 9. -/
private noncomputable def cycleRaw9 (offset degree : Nat) : PackedProgram 50 degree 9 0 := PackedProgram.read (width := 9) (PackedProgram.emit [2, 9] (offset.testBit 9 ^^ false) (by decide) (cycleRaw10 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps9 (offset : Nat) : List PackedStep := (10, true, [2, 9], 10, (offset.testBit 9 ^^ false)) :: cycleSteps10 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric9 (offset degree : Nat) :
    (cycleRaw9 offset degree).numeric =
      (fun table => (cycleSteps9 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw10 offset degree).numeric (packedStep 50 degree table (10, true, [2, 9], 10, (offset.testBit 9 ^^ false))) = _
  rw [cycle_numeric10]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 8. -/
private noncomputable def cycleRaw8 (offset degree : Nat) : PackedProgram 50 degree 8 0 := PackedProgram.read (width := 8) (PackedProgram.emit [0, 1, 8] (offset.testBit 8 ^^ true) (by decide) (cycleRaw9 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps8 (offset : Nat) : List PackedStep := (9, true, [0, 1, 8], 9, (offset.testBit 8 ^^ true)) :: cycleSteps9 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric8 (offset degree : Nat) :
    (cycleRaw8 offset degree).numeric =
      (fun table => (cycleSteps8 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw9 offset degree).numeric (packedStep 50 degree table (9, true, [0, 1, 8], 9, (offset.testBit 8 ^^ true))) = _
  rw [cycle_numeric9]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 7. -/
private noncomputable def cycleRaw7 (offset degree : Nat) : PackedProgram 50 degree 7 0 := PackedProgram.read (width := 7) (PackedProgram.emit [3, 5, 7] (offset.testBit 7 ^^ true) (by decide) (cycleRaw8 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps7 (offset : Nat) : List PackedStep := (8, true, [3, 5, 7], 8, (offset.testBit 7 ^^ true)) :: cycleSteps8 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric7 (offset degree : Nat) :
    (cycleRaw7 offset degree).numeric =
      (fun table => (cycleSteps7 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw8 offset degree).numeric (packedStep 50 degree table (8, true, [3, 5, 7], 8, (offset.testBit 7 ^^ true))) = _
  rw [cycle_numeric8]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 6. -/
private noncomputable def cycleRaw6 (offset degree : Nat) : PackedProgram 50 degree 6 0 := PackedProgram.read (width := 6) (PackedProgram.emit [0, 4, 6] (offset.testBit 6 ^^ true) (by decide) (cycleRaw7 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps6 (offset : Nat) : List PackedStep := (7, true, [0, 4, 6], 7, (offset.testBit 6 ^^ true)) :: cycleSteps7 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric6 (offset degree : Nat) :
    (cycleRaw6 offset degree).numeric =
      (fun table => (cycleSteps6 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw7 offset degree).numeric (packedStep 50 degree table (7, true, [0, 4, 6], 7, (offset.testBit 6 ^^ true))) = _
  rw [cycle_numeric7]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 5. -/
private noncomputable def cycleRaw5 (offset degree : Nat) : PackedProgram 50 degree 5 0 := PackedProgram.read (width := 5) (PackedProgram.emit [5] (offset.testBit 5 ^^ true) (by decide) (cycleRaw6 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps5 (offset : Nat) : List PackedStep := (6, true, [5], 6, (offset.testBit 5 ^^ true)) :: cycleSteps6 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric5 (offset degree : Nat) :
    (cycleRaw5 offset degree).numeric =
      (fun table => (cycleSteps5 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw6 offset degree).numeric (packedStep 50 degree table (6, true, [5], 6, (offset.testBit 5 ^^ true))) = _
  rw [cycle_numeric6]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 4. -/
private noncomputable def cycleRaw4 (offset degree : Nat) : PackedProgram 50 degree 4 0 := PackedProgram.read (width := 4) (PackedProgram.emit [0, 3, 4] (offset.testBit 4 ^^ true) (by decide) (cycleRaw5 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps4 (offset : Nat) : List PackedStep := (5, true, [0, 3, 4], 5, (offset.testBit 4 ^^ true)) :: cycleSteps5 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric4 (offset degree : Nat) :
    (cycleRaw4 offset degree).numeric =
      (fun table => (cycleSteps4 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw5 offset degree).numeric (packedStep 50 degree table (5, true, [0, 3, 4], 5, (offset.testBit 4 ^^ true))) = _
  rw [cycle_numeric5]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 3. -/
private noncomputable def cycleRaw3 (offset degree : Nat) : PackedProgram 50 degree 3 0 := PackedProgram.read (width := 3) (PackedProgram.emit [0, 3] (offset.testBit 3 ^^ false) (by decide) (cycleRaw4 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps3 (offset : Nat) : List PackedStep := (4, true, [0, 3], 4, (offset.testBit 3 ^^ false)) :: cycleSteps4 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric3 (offset degree : Nat) :
    (cycleRaw3 offset degree).numeric =
      (fun table => (cycleSteps3 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw4 offset degree).numeric (packedStep 50 degree table (4, true, [0, 3], 4, (offset.testBit 3 ^^ false))) = _
  rw [cycle_numeric4]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 2. -/
private noncomputable def cycleRaw2 (offset degree : Nat) : PackedProgram 50 degree 2 0 := PackedProgram.read (width := 2) (PackedProgram.emit [2] (offset.testBit 2 ^^ true) (by decide) (cycleRaw3 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps2 (offset : Nat) : List PackedStep := (3, true, [2], 3, (offset.testBit 2 ^^ true)) :: cycleSteps3 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric2 (offset degree : Nat) :
    (cycleRaw2 offset degree).numeric =
      (fun table => (cycleSteps2 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw3 offset degree).numeric (packedStep 50 degree table (3, true, [2], 3, (offset.testBit 2 ^^ true))) = _
  rw [cycle_numeric3]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 1. -/
private noncomputable def cycleRaw1 (offset degree : Nat) : PackedProgram 50 degree 1 0 := PackedProgram.read (width := 1) (PackedProgram.emit [0, 1] (offset.testBit 1 ^^ false) (by decide) (cycleRaw2 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps1 (offset : Nat) : List PackedStep := (2, true, [0, 1], 2, (offset.testBit 1 ^^ false)) :: cycleSteps2 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric1 (offset degree : Nat) :
    (cycleRaw1 offset degree).numeric =
      (fun table => (cycleSteps1 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw2 offset degree).numeric (packedStep 50 degree table (2, true, [0, 1], 2, (offset.testBit 1 ^^ false))) = _
  rw [cycle_numeric2]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified suffix beginning at physical coordinate 0. -/
private noncomputable def cycleRaw0 (offset degree : Nat) : PackedProgram 50 degree 0 0 := PackedProgram.read (width := 0) (PackedProgram.emit [0] (offset.testBit 0 ^^ true) (by decide) (cycleRaw1 offset degree))

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata followed by the remaining numerical updates. -/
private noncomputable def cycleSteps0 (offset : Nat) : List PackedStep := (1, true, [0], 1, (offset.testBit 0 ^^ true)) :: cycleSteps1 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One coordinate preserves agreement between the certified and flattened evaluators. -/
private theorem cycle_numeric0 (offset degree : Nat) :
    (cycleRaw0 offset degree).numeric =
      (fun table => (cycleSteps0 offset).foldl (packedStep 50 degree) table) := by
  funext table
  change (cycleRaw1 offset degree).numeric (packedStep 50 degree table (1, true, [0], 1, (offset.testBit 0 ^^ true))) = _
  rw [cycle_numeric1]
  exact List.foldl_cons.symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Coordinate metadata for the entire fast recurrence. -/
noncomputable def cycleSteps (offset : Nat) : List PackedStep := cycleSteps0 offset

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Flattened affine instruction list for the certified encoder. -/
noncomputable def cycleInstructions (offset : Nat) : List Instruction := [
  .read 0,
  .emit [0] (offset.testBit 0 ^^ true),
  .read 1,
  .emit [0, 1] (offset.testBit 1 ^^ false),
  .read 2,
  .emit [2] (offset.testBit 2 ^^ true),
  .read 3,
  .emit [0, 3] (offset.testBit 3 ^^ false),
  .read 4,
  .emit [0, 3, 4] (offset.testBit 4 ^^ true),
  .read 5,
  .emit [5] (offset.testBit 5 ^^ true),
  .read 6,
  .emit [0, 4, 6] (offset.testBit 6 ^^ true),
  .read 7,
  .emit [3, 5, 7] (offset.testBit 7 ^^ true),
  .read 8,
  .emit [0, 1, 8] (offset.testBit 8 ^^ true),
  .read 9,
  .emit [2, 9] (offset.testBit 9 ^^ false),
  .read 10,
  .emit [0, 7, 8, 9, 10] (offset.testBit 10 ^^ true),
  .read 11,
  .emit [0, 6, 7, 9, 10, 11] (offset.testBit 11 ^^ false),
  .forget 0 12,
  .read 11,
  .emit [2, 11] (offset.testBit 12 ^^ false),
  .read 12,
  .emit [2, 10, 12] (offset.testBit 13 ^^ true),
  .emit [4, 5, 6, 7, 8, 9, 11, 12] (offset.testBit 14 ^^ false),
  .read 13,
  .emit [1, 5, 7, 13] (offset.testBit 15 ^^ false),
  .emit [1, 5, 7, 9, 10, 12] (offset.testBit 16 ^^ false),
  .read 14,
  .emit [0, 4, 5, 6, 7, 8, 10, 11, 13, 14] (offset.testBit 17 ^^ false),
  .emit [3, 4, 5, 7, 8, 11, 13] (offset.testBit 18 ^^ true),
  .emit [4, 5, 8, 11, 13, 14] (offset.testBit 19 ^^ false),
  .forget 5 15,
  .read 14,
  .emit [3, 4, 14] (offset.testBit 20 ^^ true),
  .read 15,
  .emit [3, 4, 7, 8, 11, 13, 15] (offset.testBit 21 ^^ true),
  .forget 3 16,
  .read 15,
  .emit [1, 7, 8, 9, 10, 15] (offset.testBit 22 ^^ false),
  .forget 7 16,
  .read 15,
  .emit [0, 1, 4, 5, 6, 8, 9, 11, 12, 13, 15] (offset.testBit 23 ^^ true),
  .forget 1 16,
  .read 15,
  .emit [2, 7, 12, 15] (offset.testBit 24 ^^ false),
  .emit [0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 15] (offset.testBit 25 ^^ true),
  .forget 2 16,
  .read 15,
  .emit [0, 4, 6, 8, 10, 11, 15] (offset.testBit 26 ^^ true),
  .read 16,
  .emit [4, 8, 11, 13, 16] (offset.testBit 27 ^^ true),
  .read 17,
  .emit [0, 5, 9, 10, 12, 13, 17] (offset.testBit 28 ^^ true),
  .forget 13 18,
  .read 17,
  .emit [7, 9, 11, 17] (offset.testBit 29 ^^ false),
  .forget 11 18,
  .emit [1, 3, 4, 8, 9, 10, 13, 15, 16] (offset.testBit 30 ^^ true),
  .forget 9 17,
  .emit [0, 3, 5, 10, 12, 13, 15] (offset.testBit 31 ^^ true),
  .read 16,
  .emit [0, 2, 5, 6, 8, 9, 11, 14, 15, 16] (offset.testBit 32 ^^ false),
  .forget 8 17,
  .read 16,
  .emit [1, 2, 7, 8, 9, 10, 16] (offset.testBit 33 ^^ true),
  .forget 10 17,
  .emit [1, 2, 4, 5, 7, 8, 9, 10, 11] (offset.testBit 34 ^^ true),
  .forget 4 16,
  .emit [0, 2, 4, 5, 7, 8, 9, 12] (offset.testBit 35 ^^ false),
  .forget 12 15,
  .read 14,
  .emit [7, 14] (offset.testBit 36 ^^ false),
  .read 15,
  .emit [6, 12, 15] (offset.testBit 37 ^^ true),
  .emit [1, 2, 3, 4, 5, 6, 7, 14, 15] (offset.testBit 38 ^^ true),
  .read 16,
  .emit [6, 12, 15, 16] (offset.testBit 39 ^^ false),
  .read 17,
  .emit [5, 6, 12, 16, 17] (offset.testBit 40 ^^ true),
  .forget 12 18,
  .read 17,
  .emit [2, 6, 7, 14, 15, 17] (offset.testBit 41 ^^ false),
  .emit [4, 5, 7, 8, 9, 11, 14, 16, 17] (offset.testBit 42 ^^ true),
  .read 18,
  .emit [0, 5, 6, 7, 12, 13, 17, 18] (offset.testBit 43 ^^ false),
  .forget 6 19,
  .emit [0, 6, 7, 13, 16, 17] (offset.testBit 44 ^^ false),
  .forget 7 18,
  .read 17,
  .emit [0, 1, 2, 5, 9, 13, 14, 15, 17] (offset.testBit 45 ^^ true),
  .read 18,
  .emit [1, 2, 4, 5, 7, 12, 14, 15, 18] (offset.testBit 46 ^^ true),
  .forget 2 19,
  .emit [1, 4, 8, 11, 13, 14, 17] (offset.testBit 47 ^^ true),
  .emit [0, 1, 2, 7, 9, 12, 13, 14, 16] (offset.testBit 48 ^^ true),
  .forget 14 18,
  .emit [1, 3, 9, 10, 13, 14, 15] (offset.testBit 49 ^^ true),
  .emit [2, 5, 10, 12, 15, 16] (offset.testBit 50 ^^ false),
  .forget 15 17,
  .read 16,
  .emit [2, 7, 11, 13, 15, 16] (offset.testBit 51 ^^ false),
  .forget 11 17,
  .emit [1, 2, 3, 5, 6, 9, 11, 12, 13, 15] (offset.testBit 52 ^^ false),
  .forget 15 16,
  .emit [0, 1, 2, 3, 5, 7, 9, 11, 12] (offset.testBit 53 ^^ true),
  .forget 7 15,
  .read 14,
  .emit [5, 9, 14] (offset.testBit 54 ^^ true),
  .read 15,
  .emit [0, 4, 5, 6, 8, 9, 14, 15] (offset.testBit 55 ^^ false),
  .emit [4, 5, 6, 8, 13, 15] (offset.testBit 56 ^^ false),
  .read 16,
  .emit [0, 2, 4, 9, 11, 12, 16] (offset.testBit 57 ^^ true),
  .forget 0 17,
  .read 16,
  .emit [2, 4, 5, 8, 9, 11, 13, 16] (offset.testBit 58 ^^ false),
  .read 17,
  .emit [1, 3, 4, 5, 7, 13, 17] (offset.testBit 59 ^^ true),
  .forget 4 18,
  .emit [2, 4, 5, 8, 10, 11, 12, 13, 16] (offset.testBit 60 ^^ true),
  .forget 5 17,
  .read 16,
  .emit [0, 1, 2, 6, 9, 11, 12, 15, 16] (offset.testBit 61 ^^ true),
  .forget 12 17,
  .read 16,
  .emit [5, 9, 15, 16] (offset.testBit 62 ^^ false),
  .forget 9 17,
  .emit [1, 3, 4, 6, 9, 10, 12, 13, 15] (offset.testBit 63 ^^ true),
  .forget 3 16,
  .read 15,
  .emit [1, 3, 5, 8, 9, 10, 13, 15] (offset.testBit 64 ^^ false),
  .read 16,
  .emit [1, 3, 14, 16] (offset.testBit 65 ^^ false),
  .forget 1 17,
  .emit [1, 4, 6, 9, 10, 12, 13, 14] (offset.testBit 66 ^^ false),
  .read 16,
  .emit [1, 7, 8, 10, 13, 15, 16] (offset.testBit 67 ^^ true),
  .forget 8 17,
  .emit [13, 15] (offset.testBit 68 ^^ false),
  .forget 13 16,
  .emit [3, 6, 7, 8, 9, 12] (offset.testBit 69 ^^ false),
  .forget 7 15,
  .emit [0, 1, 2, 8, 10, 13] (offset.testBit 70 ^^ false),
  .forget 10 14,
  .emit [0, 2, 6, 8, 9, 11] (offset.testBit 71 ^^ false),
  .forget 2 13,
  .read 12,
  .emit [1, 2, 4, 6, 7, 9, 12] (offset.testBit 72 ^^ true),
  .read 13,
  .emit [2, 4, 11, 13] (offset.testBit 73 ^^ false),
  .forget 4 14,
  .emit [3, 4, 6, 7] (offset.testBit 74 ^^ false),
  .forget 6 13,
  .emit [1, 3, 6, 7] (offset.testBit 75 ^^ false),
  .emit [4, 7] (offset.testBit 76 ^^ false),
  .forget 7 12,
  .read 11,
  .emit [1, 3, 7, 9, 11] (offset.testBit 77 ^^ true),
  .forget 7 12,
  .emit [0, 3, 5, 7, 8, 9] (offset.testBit 78 ^^ false),
  .forget 3 11,
  .emit [1, 2, 7, 8] (offset.testBit 79 ^^ false),
  .emit [2, 4, 5] (offset.testBit 80 ^^ true),
  .forget 5 10,
  .emit [0, 1, 2, 5, 7] (offset.testBit 81 ^^ true),
  .forget 5 9,
  .emit [0, 1, 3, 6] (offset.testBit 82 ^^ false),
  .forget 1 8,
  .emit [0, 1, 3, 5] (offset.testBit 83 ^^ false),
  .forget 3 7,
  .emit [0, 1, 5] (offset.testBit 84 ^^ true),
  .forget 1 6,
  .emit [0, 1, 3] (offset.testBit 85 ^^ true),
  .forget 0 5,
  .emit [0, 2] (offset.testBit 86 ^^ false),
  .forget 2 4,
  .emit [1, 2] (offset.testBit 87 ^^ false),
  .forget 1 3,
  .emit [0] (offset.testBit 88 ^^ true),
  .forget 0 2,
  .emit [0] (offset.testBit 89 ^^ true),
  .forget 0 1]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Structural equality of the certified and efficient numeric functions. -/
private theorem cycle_raw_numeric (offset degree : Nat) : (cycleRaw0 offset degree).numeric = (fun table => (cycleSteps offset).foldl (fastPackedStep 50 degree) table) := by
  funext table
  rw [fastPackedFold_eq]
  simpa only [cycleSteps] using congrFun (cycle_numeric0 offset degree) table

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Structural equality of the certified and flattened instruction lists. -/
private theorem cycle_raw_program (offset degree : Nat) : (cycleRaw0 offset degree).certificate.program = cycleInstructions offset := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The certified encoder sums each coefficient once. -/
private theorem cycle_raw_merges (offset degree : Nat) : (cycleRaw0 offset degree).merges = 49 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified encoder with a flattened implementation for efficient kernel evaluation. -/
noncomputable def cycleProgram (offset degree : Nat) : PackedProgram 50 degree 0 0 :=
  PackedProgram.flatten (cycleRaw0 offset degree) (cycleInstructions offset)
    (fun table => (cycleSteps offset).foldl (fastPackedStep 50 degree) table) 49
    (cycle_raw_program offset degree) (cycle_raw_numeric offset degree) (cycle_raw_merges offset degree)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Certified generators paired with their coefficient inputs. -/
noncomputable def cycleInputs : List (Nat × Nat) := [
  (3419, 1),
  (12681474, 2),
  (50344452, 4),
  (3408024, 8),
  (18500960336, 16),
  (1032352, 32),
  (13061104748608, 64),
  (6802560, 128),
  (5619205376, 256),
  (1891716608, 512),
  (12184660992, 1024),
  (189494273157236736, 2048),
  (749621248, 4096),
  (36800913408, 8192),
  (414089216, 16384),
  (2158470301355737088, 32768),
  (1791035965440, 65536),
  (9813906816128516096, 131072),
  (33389633601536, 262144),
  (67460509835680808960, 524288),
  (108091492270080, 1048576),
  (1117108528687874048, 2097152),
  (7418312659260407808, 4194304),
  (546276422539532042240, 8388608),
  (2396957360259072, 16777216),
  (167570080135160791040, 33554432),
  (1430777276092727164928, 67108864),
  (534706248482816, 134217728),
  (1797564072460288, 268435456),
  (8186413824606208, 536870912),
  (3617878140010889216, 1073741824),
  (11643828138147840, 2147483648),
  (26648740273861624332288, 4294967296),
  (738446962572499353600, 8589934592),
  (3545683212572605546496, 17179869184),
  (162925550531679503777792, 34359738368),
  (137059362510857496952832, 68719476736),
  (510677465179957070135296, 137438953472),
  (75259176495831015648919552, 274877906944),
  (1511181774100259363880960, 549755813888),
  (14251839179197538893824, 1099511627776),
  (81617335535437777840635904, 2199023255552),
  (2878978735897831293321216, 4398046511104),
  (14508751595598110246567936, 8796093022208),
  (8053073699330494434377728, 17592186044416),
  (223353324818427840642940928, 35184372088832),
  (817276355357835148908298240, 70368744177664),
  (388169080158919097275383808, 140737488355328),
  (32489881402143159070228480, 281474976710656)]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Generators encoded by the trellis. -/
noncomputable def cycleGenerators : List Nat := cycleInputs.map Prod.fst

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The encoder has the required number of reads. -/
theorem cycle_reads (offset : Nat) : reads (cycleInstructions offset) = 49 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The encoder has the required number of outputs. -/
theorem cycle_outputs (offset : Nat) : outputs (cycleInstructions offset) = 90 := by rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The encoder sums each coefficient once. -/
private theorem cycle_merges (offset degree : Nat) : (cycleProgram offset degree).merges = 49 := by rfl

end Quantum.Stabilizer.Homological.F2Mask.Trellis.Bravyi90

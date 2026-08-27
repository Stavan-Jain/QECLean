/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.ClassData

/-!
# Z5Z15F2A6 dispatch certificates

Batched kernel certificates tying every `ClassData` table entry to the
semantic objects of the instance bundle.  Each theorem is one
`native_decide` over the finite index range; the per-class content is
documented in `ClassData.lean`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-- Every class rep has the tabulated weight, and it is light and even. -/
theorem rep_weight_certs : ∀ i : Fin 113,
    (Finset.univ.filter fun j : G150 × Fin 2 => repChain i j ≠ 0).card
      = BW.getD i.val 0 := by
  native_decide

/-- Arithmetic shape of the class weights: `1 ≤ t` and `|b| + 2t = 16`. -/
theorem class_t_certs : ∀ i : Fin 113,
    1 ≤ tOf i ∧ BW.getD i.val 0 + 2 * tOf i = 16 := by
  native_decide

/-- Small classes: the tabulated preimage hits the tabulated translate of
the rep. -/
theorem s_translate_certs : ∀ i : Fin 113, KIND.getD i.val 0 = 0 →
    bbBoundary2Fn a150 b150 (sF0Chain i)
      = translate1 (sShiftEl i) (repChain i) := by
  native_decide

/-- Small classes: the tabulated preimage is seam-good. -/
theorem s_seam_certs : ∀ i : Fin 113, KIND.getD i.val 0 = 0 →
    ∀ j : G150 × Fin 2,
      coverData.sheet0 (coverData.liftStab (sF0Chain i)) j ≠ 0 →
      bbBoundary2Fn a150 b150 (sF0Chain i) j ≠ 0 := by
  native_decide

/-- Window classes: the tabulated preimage hits the rep itself. -/
theorem win_f0_certs : ∀ i : Fin 113, KIND.getD i.val 0 = 1 →
    bbBoundary2Fn a150 b150 (winF0Chain i) = repChain i := by
  native_decide

/-- Window classes: the mask is exactly `supp b ∪ seam`. -/
theorem win_mem_certs : ∀ i : Fin 113, KIND.getD i.val 0 = 1 →
    ∀ j : G150 × Fin 2,
      winMem i j = true ↔
        (bbBoundary2Fn a150 b150 (winF0Chain i) j ≠ 0 ∨
         coverData.sheet0 (coverData.liftStab (winF0Chain i)) j ≠ 0) := by
  native_decide

/-- Window classes: the tabulated cycle is a boundary supported in the
window. -/
theorem win_z_certs : ∀ i : Fin 113, KIND.getD i.val 0 = 1 →
    bbBoundary2Fn a150 b150 (winZPreChain i) = winZChain i ∧
    ∀ j : G150 × Fin 2, winZChain i j ≠ 0 → winMem i j = true := by
  native_decide

/-- Extra-cell cycles: each is a boundary supported in its window plus its
extra cell. -/
theorem x_z_certs : ∀ e : Fin nExtras,
    bbBoundary2Fn a150 b150 (xZPreChain e) = xZChain e ∧
    ∀ j : G150 × Fin 2, xZChain e j ≠ 0 →
      (winMem (xClsIdx e) j = true ∨ cellIdx j = XCELL.getD e.val 0) := by
  native_decide

/-- The flat `∂₁`-column table matches the boundary map on the `δ`-basis. -/
theorem col_certs : ∀ j : G150 × Fin 2,
    bbBoundary1Fn a150 b150 (Pi.single j 1) = colFn j := by
  native_decide

/-- Parity basis: every generator boundary has even total (`ZMod 2` sum
zero). -/
theorem parity_basis_certs : ∀ g : G150,
    (∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 (Pi.single g 1) j) = 0 := by
  native_decide

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

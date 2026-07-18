/-
# Sweep leaf: the light-boundary classification (`light_boundary_classification_mask`)

One `2¹⁸` kernel sweep (own file for parallel builds — see
`MaskDefs.lean`): every nonzero base boundary of weight ≤ 7 has weight
exactly 6 and a seam-good preimage in its `ker ∂₂` fiber.

The hypothesis/count side of the sweep runs on the bitmask form (`natWt`/
`bndMask`, `MaskDefs.lean`); only the light masks that survive it evaluate the
`SeamGood` conclusion.  The public statement is recovered through the mask
bridges.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.MaskDefs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

private theorem classify_fast : ∀ m : Fin (2 ^ 18),
    bndMask m.val ≠ 0 → natWt 36 (bndMask m.val) ≤ 7 →
    natWt 36 (bndMask m.val) = 6 ∧
    ∃ c0 c1 : ZMod 2, SeamGood (chainOf m.val + kcombo c0 c1) := by
  native_decide

theorem light_boundary_classification_mask :
    ∀ m : Fin (2 ^ 18),
      bbBoundary2Fn a36 b36 (chainOf m.val) ≠ 0 →
      (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 (chainOf m.val) j ≠ 0).card ≤ 7 →
      (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 (chainOf m.val) j ≠ 0).card = 6 ∧
      ∃ c0 c1 : ZMod 2, SeamGood (chainOf m.val + kcombo c0 c1) := by
  intro m hne hle
  have hmask_ne : bndMask m.val ≠ 0 := fun h0 => hne ((bnd_eq_zero_iff m.isLt).mpr h0)
  have hcard : (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 (chainOf m.val) j ≠ 0).card
      = natWt 36 (bndMask m.val) := by
    rw [card_support_eq_natWt, bnd_c1MaskOf m.isLt]
  rw [hcard] at hle ⊢
  exact classify_fast m hmask_ne hle

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

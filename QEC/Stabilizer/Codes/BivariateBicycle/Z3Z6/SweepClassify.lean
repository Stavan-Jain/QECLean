/-
# Sweep leaf: the light-boundary classification (`light_boundary_classification_mask`)

One `2¹⁸` kernel sweep (own file for parallel builds — see
`MaskDefs.lean`): every nonzero base boundary of weight ≤ 7 has weight
exactly 6 and a seam-good preimage in its `ker ∂₂` fiber.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.MaskDefs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

theorem light_boundary_classification_mask :
    ∀ m : Fin (2 ^ 18),
      bbBoundary2Fn a36 b36 (chainOf m.val) ≠ 0 →
      (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 (chainOf m.val) j ≠ 0).card ≤ 7 →
      (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 (chainOf m.val) j ≠ 0).card = 6 ∧
      ∃ c0 c1 : ZMod 2, SeamGood (chainOf m.val + kcombo c0 c1) := by
  native_decide

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

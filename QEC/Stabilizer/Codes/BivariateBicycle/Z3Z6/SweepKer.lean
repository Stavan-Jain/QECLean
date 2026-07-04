/-
# Sweep leaf: `ker ∂₂` spanning (`ker_vanish_free_mask`)

One `2¹⁸` kernel sweep (own file for parallel builds — see
`MaskDefs.lean`): a base 2-cycle vanishing at both free cells is zero.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.MaskDefs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

theorem ker_vanish_free_mask :
    ∀ m : Fin (2 ^ 18),
      bbBoundary2Fn a36 b36 (chainOf m.val) = 0 →
      chainOf m.val (0, 0) = 0 → chainOf m.val (0, 1) = 0 →
      chainOf m.val = 0 := by
  native_decide

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

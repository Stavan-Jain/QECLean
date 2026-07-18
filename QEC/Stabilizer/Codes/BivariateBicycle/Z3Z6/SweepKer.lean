/-
# Sweep leaf: `ker ∂₂` spanning (`ker_vanish_free_mask`)

One `2¹⁸` kernel sweep (own file for parallel builds — see
`MaskDefs.lean`): a base 2-cycle vanishing at both free cells is zero.

The sweep itself runs on the bitmask form (`bndMask`, `MaskDefs.lean`); the
public statement is recovered through the mask bridges.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.MaskDefs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

private theorem ker_fast : ∀ m : Fin (2 ^ 18),
    bndMask m.val = 0 → m.val.testBit 0 = false → m.val.testBit 1 = false →
    m.val = 0 := by
  native_decide

theorem ker_vanish_free_mask :
    ∀ m : Fin (2 ^ 18),
      bbBoundary2Fn a36 b36 (chainOf m.val) = 0 →
      chainOf m.val (0, 0) = 0 → chainOf m.val (0, 1) = 0 →
      chainOf m.val = 0 := by
  intro m hb h00 h01
  have hidx0 : idxOf36 ((0 : ZMod 3), (0 : ZMod 6)) = 0 := by decide
  have hidx1 : idxOf36 ((0 : ZMod 3), (1 : ZMod 6)) = 1 := by decide
  have hm0 : m.val = 0 := by
    apply ker_fast m ((bnd_eq_zero_iff m.isLt).mp hb)
    · have h := (chainOf_apply_eq_zero_iff m.val ((0 : ZMod 3), (0 : ZMod 6))).mp h00
      rwa [hidx0] at h
    · have h := (chainOf_apply_eq_zero_iff m.val ((0 : ZMod 3), (1 : ZMod 6))).mp h01
      rwa [hidx1] at h
  rw [hm0]
  exact chainOf_zero

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

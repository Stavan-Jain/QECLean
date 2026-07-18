/-
# Sweep leaf: Smith-class `(0,1)` coset floor (`leaf_floor_01_mask`)

One `2¹⁸` kernel sweep (own file for parallel builds — see
`MaskDefs.lean`): every element of the seam-coset of `kcombo 0 1` has
weight ≥ 8.  Sweeps against the tabulated seam `seam01`
(`SeamTables.lean`) — the closed `seamC` term would otherwise be
re-derived at every (mask, cell) pair.  SAT cross-check: class minimum
exactly 8.

The sweep itself runs on the bitmask form (`natWt`/`bndMask`/`seam01Mask`,
`MaskDefs.lean`/`SeamTables.lean`) — pure `Nat` ops per mask — and the public
statement is recovered through the mask bridges (`card_support_eq_natWt`,
`bnd_c1MaskOf`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SeamTables

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

private theorem leaf01_fast : ∀ m : Fin (2 ^ 18),
    8 ≤ natWt 36 (seam01Mask ^^^ bndMask m.val) := by
  native_decide

theorem leaf_floor_01_mask : ∀ m : Fin (2 ^ 18),
    8 ≤ (Finset.univ.filter fun j : G36 × Fin 2 =>
      (seam01 + bbBoundary2Fn a36 b36 (chainOf m.val)) j ≠ 0).card := by
  intro m
  have hmask : c1MaskOf (seam01 + bbBoundary2Fn a36 b36 (chainOf m.val))
      = seam01Mask ^^^ bndMask m.val := by
    rw [c1MaskOf_add, seam01Mask_eq, bnd_c1MaskOf m.isLt]
  rw [card_support_eq_natWt, hmask]
  exact leaf01_fast m

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

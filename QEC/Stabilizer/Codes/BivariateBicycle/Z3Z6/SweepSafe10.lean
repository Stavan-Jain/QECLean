/-
# Sweep leaf: Smith-class `(1,0)` coset floor (`leaf_floor_10_mask`)

One `2¹⁸` kernel sweep (own file for parallel builds — see
`MaskDefs.lean`): every element of the seam-coset of `kcombo 1 0` has
weight ≥ 8.  Sweeps against the tabulated seam `seam10`
(`SeamTables.lean`) — the closed `seamC` term would otherwise be
re-derived at every (mask, cell) pair.  SAT cross-check: class minimum
exactly 8.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SeamTables

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

theorem leaf_floor_10_mask : ∀ m : Fin (2 ^ 18),
    8 ≤ (Finset.univ.filter fun j : G36 × Fin 2 =>
      (seam10 + bbBoundary2Fn a36 b36 (chainOf m.val)) j ≠ 0).card := by
  native_decide

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

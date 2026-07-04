/-
# The dangerous sector of the [[72,4,8]] cover: `≥ 8` at nonzero slice

`pair72_dangerousFloorNZ : coverData.DangerousFloorNZ 8` — every
nontrivial cover cycle whose pushforward is a nonzero base boundary has
weight ≥ 8.

Dispatch: if `|p(v)| ≥ 8` we are done by the slice inequality; otherwise
the light-boundary classification pins `p(v)` to a weight-6 boundary with
a seam-good preimage `f₀`, and the generic single-shape rung
(`dangerous_bound_of_single_shape`, `d = 4`, `t = 1`) closes the case.
Unlike gross (hexagons + D-pairs), ONE rung shape suffices here — the
classification hands every light class to it directly.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.LightStab
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.BaseDistance

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

-- Defeq checks through `coverData`'s complex projections unfold deep
-- `Prod`/`ZMod` instance chains (same as the gross instance files).
set_option maxRecDepth 4096

/-- **The dangerous floor at nonzero slice.** -/
theorem pair72_dangerousFloorNZ : coverData.DangerousFloorNZ 8 := by
  intro v hv hnb hbmem hbne
  -- destructure the boundary membership with `f` born over the concrete
  -- group type (the submodule's own carrier is only defeq to it, which
  -- typeclass synthesis cannot see through)
  obtain ⟨f, hf'⟩ : ∃ f : G36 → ZMod 2,
      bbBoundary2Fn a36 b36 f = coverData.push1 v := by
    obtain ⟨fraw, hfraw⟩ := hbmem
    exact ⟨fraw, hfraw⟩
  by_cases hw : 8 ≤ coverData.baseComplex.chainWeight (coverData.push1 v)
  · exact le_trans hw (coverData.chainWeight_push_le v)
  · push Not at hw
    have hne : bbBoundary2Fn a36 b36 f ≠ 0 := by
      rw [hf']
      exact hbne
    have hle : (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 f j ≠ 0).card ≤ 7 := by
      have heq : (Finset.univ.filter fun j : G36 × Fin 2 =>
          bbBoundary2Fn a36 b36 f j ≠ 0).card
          = coverData.baseComplex.chainWeight (coverData.push1 v) := by
        rw [coverData.baseComplex_chainWeight_eq, hf']
      omega
    obtain ⟨hw6, c0, c1, hseam⟩ := light_boundary_classification f hne hle
    -- the seam-good preimage of the same boundary
    set f₀ : G36 → ZMod 2 := f + kcombo c0 c1 with hf₀def
    have hsame : bbBoundary2Fn a36 b36 f₀ = bbBoundary2Fn a36 b36 f := by
      rw [hf₀def, bbBoundary2Fn_add, kcombo_mem_ker, add_zero]
    have hwb : coverData.baseComplex.chainWeight (bbBoundary2Fn a36 b36 f₀)
        + 2 * 1 = 2 * 4 := by
      rw [coverData.baseComplex_chainWeight_eq, hsame, hw6]
    have h8 : 2 * 4 ≤ coverData.coverComplex.chainWeight v := by
      refine coverData.dangerous_bound_of_single_shape
        base36_strong_floor le_rfl f₀ hwb hseam hv hnb ?_
      change coverData.push1 v = bbBoundary2Fn a36 b36 f₀
      rw [hsame, hf']
    omega

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

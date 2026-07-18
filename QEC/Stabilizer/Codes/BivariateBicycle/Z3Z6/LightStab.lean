/-
# Light boundaries of the [[36,4,4]] base: census and seam-good preimages

The chain-level statements consumed by the dangerous- and safe-sector
floors, obtained from the mask-quantified sweep leaves (`SweepKer.lean`,
`SweepClassify.lean`) through the `chainOf_maskOf` round trip
(`MaskDefs.lean`):

* `ker_vanish_free` / `ker_eq_kcombo` — the **direct spanning argument**:
  a base 2-cycle is the systematic `kcombo` of its free-cell values (no
  factorization certificate needed at this scale);
* `light_boundary_classification` — every nonzero base boundary of weight
  ≤ 7 has weight exactly 6, and its `ker ∂₂` fiber contains a *seam-good*
  preimage — exactly the hypothesis of the generic single-shape rung.

Provenance/cross-check: `qec-lab:experiments/bb_lab/scripts/gen_pair72_z6z6_data.py`
§§2,5 (census `{6: 24}`, all 24 classes seam-good).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepKer
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepClassify

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-- **Direct spanning sweep**: a base 2-cycle vanishing at both free cells
is zero.  (The `dim ker ∂₂ = 2` fact.) -/
theorem ker_vanish_free :
    ∀ ζ : G36 → ZMod 2, bbBoundary2Fn a36 b36 ζ = 0 →
      ζ (0, 0) = 0 → ζ (0, 1) = 0 → ζ = 0 := by
  intro ζ h1 h2 h3
  have hm := ker_vanish_free_mask ⟨maskOf ζ, maskOf_lt ζ⟩
  rw [chainOf_maskOf ζ] at hm
  exact hm h1 h2 h3

/-- Every base 2-cycle is the systematic combination of its free-cell
values. -/
theorem ker_eq_kcombo {ζ : G36 → ZMod 2}
    (hζ : bbBoundary2Fn a36 b36 ζ = 0) :
    ζ = kcombo (ζ (0, 0)) (ζ (0, 1)) := by
  set c0 := ζ (0, 0)
  set c1 := ζ (0, 1)
  have hk : bbBoundary2Fn a36 b36 (kcombo c0 c1) = 0 := kcombo_mem_ker c0 c1
  have hsum : bbBoundary2Fn a36 b36 (ζ + kcombo c0 c1) = 0 := by
    rw [bbBoundary2Fn_add, hζ, hk, add_zero]
  have h0 : (ζ + kcombo c0 c1) (0, 0) = 0 := by
    rw [Pi.add_apply, (kcombo_at_free c0 c1).1]
    exact CharTwo.add_self_eq_zero _
  have h1 : (ζ + kcombo c0 c1) (0, 1) = 0 := by
    rw [Pi.add_apply, (kcombo_at_free c0 c1).2]
    exact CharTwo.add_self_eq_zero _
  have hzero := ker_vanish_free _ hsum h0 h1
  funext g
  have hg := congrFun hzero g
  rw [Pi.add_apply, Pi.zero_apply] at hg
  have hkey : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact hkey _ _ hg

/-- **The classification sweep**: every nonzero base boundary of weight
≤ 7 has weight exactly 6, and some preimage in the `ker ∂₂` fiber is
seam-good. -/
theorem light_boundary_classification :
    ∀ f : G36 → ZMod 2,
      bbBoundary2Fn a36 b36 f ≠ 0 →
      (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 f j ≠ 0).card ≤ 7 →
      (Finset.univ.filter fun j : G36 × Fin 2 =>
        bbBoundary2Fn a36 b36 f j ≠ 0).card = 6 ∧
      ∃ c0 c1 : ZMod 2, SeamGood (f + kcombo c0 c1) := by
  intro f hne hle
  have hm := light_boundary_classification_mask ⟨maskOf f, maskOf_lt f⟩
  rw [chainOf_maskOf f] at hm
  exact hm hne hle

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

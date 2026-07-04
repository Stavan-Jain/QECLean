/-
# The Smith-coset floor of the [[36,4,4]] base: `SeamCosetFloor 8`

`pair72_seamCosetFloor : coverData.SeamCosetFloor 8` — every chain in a
seam-coset `seamC ζ + im ∂₂` (`ζ ∈ ker ∂₂`) that is not itself a base
boundary has weight ≥ 8.  This is the (M-im) analog of the gross proof at
1/16th the dispatch: `ker ∂₂` has dimension 2, so there are three nonzero
Smith classes, each handled by ONE direct 2¹⁸ kernel sweep — no CRT
engine, no orbit transport, no slab filters (contrast
`Codes/BivariateBicycle/MImFloor*.lean`).

The three per-class sweeps live in `SweepSafe{10,01,11}.lean` (parallel
build leaves); this file restores their ∀-chain forms via
`chainOf_maskOf` and assembles the dispatch.  The class minima are
exactly 8 (SAT cross-checks in `gen_pair72_z6z6_data.py` and
`verify_doubling_pair_z3z6.py`); the zero class is vacuous (its coset
consists of boundaries).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepSafe10
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepSafe01
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepSafe11
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.LightStab

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-! ## The three per-class floors, in ∀-chain form -/

theorem leaf_floor_10 : ∀ f : G36 → ZMod 2,
    8 ≤ (Finset.univ.filter fun j : G36 × Fin 2 =>
      (coverData.seamC (kcombo 1 0) + bbBoundary2Fn a36 b36 f) j ≠ 0).card := by
  intro f
  rw [seamC_eq_seam10]
  have h := leaf_floor_10_mask ⟨maskOf f, maskOf_lt f⟩
  rwa [chainOf_maskOf f] at h

theorem leaf_floor_01 : ∀ f : G36 → ZMod 2,
    8 ≤ (Finset.univ.filter fun j : G36 × Fin 2 =>
      (coverData.seamC (kcombo 0 1) + bbBoundary2Fn a36 b36 f) j ≠ 0).card := by
  intro f
  rw [seamC_eq_seam01]
  have h := leaf_floor_01_mask ⟨maskOf f, maskOf_lt f⟩
  rwa [chainOf_maskOf f] at h

theorem leaf_floor_11 : ∀ f : G36 → ZMod 2,
    8 ≤ (Finset.univ.filter fun j : G36 × Fin 2 =>
      (coverData.seamC (kcombo 1 1) + bbBoundary2Fn a36 b36 f) j ≠ 0).card := by
  intro f
  rw [seamC_eq_seam11]
  have h := leaf_floor_11_mask ⟨maskOf f, maskOf_lt f⟩
  rwa [chainOf_maskOf f] at h

/-! ## Assembly: the Smith-coset floor -/

/-- **The seam-coset floor at 8** (the (M-im) analog). -/
theorem pair72_seamCosetFloor : coverData.SeamCosetFloor 8 := by
  intro ζ hζ f hnb
  have hz := ker_eq_kcombo hζ
  have hval : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [coverData.baseComplex_chainWeight_eq]
  rcases hval (ζ (0, 0)) with hc0 | hc0 <;>
    rcases hval (ζ (0, 1)) with hc1 | hc1 <;>
    rw [hc0, hc1] at hz
  -- zero class: vacuous, the coset consists of boundaries
  · exfalso
    apply hnb
    have hzero : ζ = 0 := by
      rw [hz]
      funext g
      have hk : ∀ g : G36, kcombo 0 0 g = 0 := by native_decide
      exact hk g
    rw [hzero, coverData.seamC_zero, zero_add]
    exact ⟨f, rfl⟩
  -- the three nonzero classes
  · rw [hz]
    exact leaf_floor_01 f
  · rw [hz]
    exact leaf_floor_10 f
  · rw [hz]
    exact leaf_floor_11 f

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum

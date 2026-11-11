import QEC.Stabilizer.Framework.Homological.BBDoubling

/-!
# Seam cosets, the kernel of the pullback, and the parity of the floors

Let `D : XDoubleCoverData G H` be a free double cover of bivariate bicycle
codes, with pushforward `p = push1`, pullback `τ = pull1` and deck translation
`σ = deckShift1` on 1-chains. A *seam coset* is the set of base 1-chains
`seamC ζ + ∂₂ f` for a fixed base 2-cycle `ζ` (`∂₂ ζ = 0`) and arbitrary `f`;
the hypothesis `SeamCosetFloor m` of the doubling theorem bounds the weight of
these chains from below. This file identifies the union of the seam cosets with
the base chains whose pullback is a cover boundary, and shows that the floors
of the doubling theorem only need to be checked at odd values when the
polynomials have an odd number of terms.

## Main statements

* `pull1_seamC`: `τ (seamC ζ) = liftStab ζ` for a base 2-cycle `ζ`.
* `pull1_mem_boundaries_iff_seamCoset`: a base 1-chain `w` pulls back to a
  cover boundary iff `w = seamC ζ + ∂₂ f` for some base 2-cycle `ζ` and some
  `f`. On homology, the kernel of `τ` on `H₁` of the base is the image of the
  connecting map `ζ ↦ [seamC ζ]`.
* `push1_mem_seamCoset_of_deckTrivial`: if the deck translation acts trivially
  on `H₁` of the cover, the pushforward of every cover cycle `v` lies in a seam
  coset, because `τ (p v) = v + σ v` is a cover boundary.
* `not_seamCosetFloor_of_light_cover_cycle`: under the same hypothesis, a cover
  cycle of weight `< m` whose pushforward is not a base boundary refutes
  `SeamCosetFloor m`.
* `base_cycle_weight_even`, `cover_cycle_weight_even`: if the base polynomials
  each have an odd number of terms, base and cover cycles have even weight.
* `seamCosetFloor_of_even_of_pred`, `safeFloor_of_even_of_pred`: under that
  parity hypothesis and for even `m`, the floor at `m - 1` implies the floor at
  `m`. Equivalently, if a floor fails at an even `m`, it is violated by a chain
  of weight at most `m - 2`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## Parity of cycles -/

/-- If the base polynomials each have an odd number of terms, every base
1-cycle has even weight. -/
theorem base_cycle_weight_even
    (hA : ∑ h, D.Ab h = 1) (hB : ∑ h, D.Bb h = 1)
    {u : H × Fin 2 → ZMod 2} (hu : u ∈ D.baseComplex.cycles) :
    Even (D.baseComplex.chainWeight u) :=
  cycle_support_even D.Ab D.Bb hA hB hu

/-- If the base polynomials each have an odd number of terms, every cover
1-cycle has even weight: the cover polynomials have the same sums as the base
ones, because the pushforward preserves the sum of the values. -/
theorem cover_cycle_weight_even
    (hA : ∑ h, D.Ab h = 1) (hB : ∑ h, D.Bb h = 1)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles) :
    Even (D.coverComplex.chainWeight v) :=
  cycle_support_even D.Ac D.Bc
    ((sum_fiberSumFn ⇑D.proj D.Ac).symm.trans (by rw [D.push_A, hA]))
    ((sum_fiberSumFn ⇑D.proj D.Bc).symm.trans (by rw [D.push_B, hB])) hv

/-! ## Seam cosets pull back to boundaries -/

/-- `τ (seamC ζ) = liftStab ζ` for a base 2-cycle `ζ`: the lifted stabilizer
of `ζ` has zero pushforward `∂₂ ζ`, so it is the pullback of a base chain,
which is its restriction to either sheet. -/
theorem pull1_seamC {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    D.pull1 (D.seamC ζ) = D.liftStab ζ := by
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp ((D.push1_liftStab ζ).trans hζ)
  rw [seamC, hu, D.sheet1_pull1]

/-- Every element `seamC ζ + ∂₂ f` of a seam coset pulls back to a cover
boundary. -/
theorem pull1_seamCoset_mem_boundaries {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) (f : H → ZMod 2) :
    D.pull1 (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f)
      ∈ D.coverComplex.boundaries := by
  rw [map_add, D.pull1_seamC hζ]
  exact add_mem (D.liftStab_mem_boundaries ζ) (D.pull1_mem_boundaries ⟨f, rfl⟩)

/-! ## The two sheets of a cover 2-chain -/

/-- The deck translation on `G` has no fixed points. -/
lemma deckSigma0_ne (g : G) : g + D.deckS ≠ g := fun h =>
  D.deckS_ne_zero (add_eq_left.mp h)

/-- Two-point fiber formula for the pushforward on chains indexed by `G`:
`(p z) (proj g) = z g + z (g + deckS)`. -/
lemma push0_pair (z : G → ZMod 2) (g : G) :
    fiberSumFn ⇑D.proj z (D.proj g) = z g + z (g + D.deckS) :=
  fiberSumFn_pair D.deckSigma0_ne D.proj_fiber z g

/-- The two sheets of a chain indexed by `G` add up to its pushforward. -/
lemma sheetC2_0_add_sheetC2_1 (z : G → ZMod 2) :
    D.sheetC2_0 z + D.sheetC2_1 z = D.push0 z :=
  funext fun h => (D.push0_pair z (D.sec h)).symm.trans
    (congrArg (fiberSumFn ⇑D.proj z) (D.proj_sec h))

/-! ## The kernel of the pullback -/

/-- A base 1-chain `w` whose pullback is a cover boundary lies in a seam coset.
Write `τ w = ∂₂ c` and let `ξ₀`, `ξ₁` be the two sheets of `c`. Then
`ξ₀ + ξ₁ = p c` is a base 2-cycle, and reading off sheet 1 of
`τ w = liftStab ξ₀ + σ (liftStab ξ₁)` gives
`w = seamC ξ₀ + seamN ξ₁ = seamC (ξ₀ + ξ₁) + ∂₂ ξ₁`. -/
theorem exists_seamCoset_of_pull1_mem_boundaries {w : H × Fin 2 → ZMod 2}
    (hbd : D.pull1 w ∈ D.coverComplex.boundaries) :
    ∃ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 ∧
      ∃ f : H → ZMod 2, w = D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f := by
  obtain ⟨c, hc⟩ := hbd
  replace hc : bbBoundary2Fn D.Ac D.Bc c = D.pull1 w := hc
  refine ⟨D.sheetC2_0 c + D.sheetC2_1 c, ?_, D.sheetC2_1 c, ?_⟩
  · rw [D.sheetC2_0_add_sheetC2_1]
    exact (D.push_boundary2_comm c).symm.trans
      ((congrArg D.push1 hc).trans (D.push1_pull1_eq_zero w))
  · have hsplit : D.pull1 w
        = D.liftStab (D.sheetC2_0 c) + D.deckShift1 (D.liftStab (D.sheetC2_1 c)) := by
      rw [← D.liftStab_deckShift, liftStab, ← bbBoundary2Fn_add, ← D.liftC2_decomp c, hc]
    have hw : w = D.seamC (D.sheetC2_0 c) + D.seamN (D.sheetC2_1 c) := by
      rw [← D.sheet1_pull1 w, hsplit, D.sheet1_add, D.sheet1_deckShift1]
      rfl
    rw [hw, D.seamC_add, ← D.seamN_add_seamC (D.sheetC2_1 c), add_add_add_comm,
      ZModModule.add_self, add_zero]

/-- A base 1-chain pulls back to a cover boundary iff it lies in a seam coset:
`τ w ∈ im ∂₂ ↔ w = seamC ζ + ∂₂ f` for some base 2-cycle `ζ` and some `f`. -/
theorem pull1_mem_boundaries_iff_seamCoset (w : H × Fin 2 → ZMod 2) :
    D.pull1 w ∈ D.coverComplex.boundaries
      ↔ ∃ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 ∧
          ∃ f : H → ZMod 2, w = D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f :=
  ⟨D.exists_seamCoset_of_pull1_mem_boundaries, fun ⟨_, hζ, f, hw⟩ =>
    hw ▸ D.pull1_seamCoset_mem_boundaries hζ f⟩

/-! ## Pushforwards of cover cycles -/

/-- If the deck translation acts trivially on `H₁` of the cover, the
pushforward of every cover 1-cycle `v` lies in a seam coset, because
`τ (p v) = v + σ v` is a cover boundary. -/
theorem push1_mem_seamCoset_of_deckTrivial (hR : D.DeckTrivialOnH1)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles) :
    ∃ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 ∧
      ∃ f : H → ZMod 2,
        D.push1 v = D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f :=
  D.exists_seamCoset_of_pull1_mem_boundaries (by
    rw [D.pull1_push1]
    exact hR v hv)

/-- If the deck translation acts trivially on `H₁` of the cover, a cover
1-cycle of weight `< m` whose pushforward is not a base boundary refutes
`SeamCosetFloor m`. This is the contrapositive of
`safeFloor_of_seamCosetFloor`. -/
theorem not_seamCosetFloor_of_light_cover_cycle (hR : D.DeckTrivialOnH1)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles)
    (hpush : D.push1 v ∉ D.baseComplex.boundaries)
    {m : ℕ} (hm : D.coverComplex.chainWeight v < m) :
    ¬ D.SeamCosetFloor m := fun hSF =>
  (D.safeFloor_of_seamCosetFloor hR hSF v hv hpush).not_gt hm

/-! ## The floors at even values -/

/-- Every element `seamC ζ + ∂₂ f` of a seam coset is a base 1-cycle. -/
lemma seamCoset_mem_cycles {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) (f : H → ZMod 2) :
    D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f ∈ D.baseComplex.cycles :=
  add_mem (D.seamC_mem_cycles hζ) (D.baseComplex.boundaries_le_cycles ⟨f, rfl⟩)

/-- An even number that is at least `m - 1` for an even `m` is at least `m`. -/
private lemma le_of_even_of_pred_le {m w : ℕ} (hm : Even m) (hw : Even w)
    (h : m - 1 ≤ w) : m ≤ w := by
  obtain ⟨s, rfl⟩ := hm
  obtain ⟨t, rfl⟩ := hw
  omega

/-- If the base polynomials each have an odd number of terms and `m` is even,
`SeamCosetFloor (m - 1)` implies `SeamCosetFloor m`: the elements of a seam
coset are cycles, so they have even weight. -/
theorem seamCosetFloor_of_even_of_pred
    (hA : ∑ h, D.Ab h = 1) (hB : ∑ h, D.Bb h = 1)
    {m : ℕ} (hm : Even m)
    (h : D.SeamCosetFloor (m - 1)) : D.SeamCosetFloor m := fun ζ hζ f hnb =>
  le_of_even_of_pred_le hm
    (D.base_cycle_weight_even hA hB (D.seamCoset_mem_cycles hζ f)) (h ζ hζ f hnb)

/-- If the base polynomials each have an odd number of terms and `m` is even,
`SafeFloor (m - 1)` implies `SafeFloor m`: cover cycles have even weight. -/
theorem safeFloor_of_even_of_pred
    (hA : ∑ h, D.Ab h = 1) (hB : ∑ h, D.Bb h = 1)
    {m : ℕ} (hm : Even m)
    (h : D.SafeFloor (m - 1)) : D.SafeFloor m := fun v hv hpush =>
  le_of_even_of_pred_le hm (D.cover_cycle_weight_even hA hB hv) (h v hv hpush)

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum

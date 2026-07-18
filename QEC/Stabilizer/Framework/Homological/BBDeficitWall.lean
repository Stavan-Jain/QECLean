/-
# The deficit wall: parity, the seam transfer kernel, and the pushforward bound

Lean layer for A17-P3 (`experiments/bb_lab/notes/A17_deficit_wall.md`): why
the safe floor of a non-doubling BB cover fails by at least two.

* **Parity (L1).** With odd-weight polynomials (`∑ A = ∑ B = 1` in
  `ZMod 2`) every 1-cycle of a BB complex has even weight — the
  augmentation `v ↦ ∑ v` is multiplicative on convolutions
  (`sum_conv`), so `B⋆v_L = A⋆v_R` forces `∑ v_L = ∑ v_R`.
  Consequently the seam-coset floor upgrades across odd values for
  free: `SeamCosetFloor (m - 1) → SeamCosetFloor m` for even `m`
  (`seamCosetFloor_of_even_of_pred`), i.e. **the maximal failing value
  of an even target `m` is `m − 2` — the deficit wall.**  The same
  holds for the cover-side `SafeFloor` (`safeFloor_of_even_of_pred`).

* **The seam transfer kernel (L0).** A base 1-chain pulls back to a
  cover *boundary* iff it lies in a seam coset:
  `pull1 w ∈ boundaries(cover) ↔ ∃ ζ ∈ ker ∂₂, ∃ f, w = seamC ζ + ∂₂ f`
  (`pull1_mem_boundaries_iff_seamCoset`).  The forward chase descends
  the boundary witness through `liftC2_decomp`; the reverse is
  `pull1_seamC : τ(seamC ζ) = liftStab ζ`.  This is the connecting-map
  slot of the transfer LES (`im δ₂ = ker τ₁`), sibling to
  `BBTransferH1.ker_pushH1_eq_range_pullH1`.

* **The pushforward bound (T2).** Under the deck homotopy (R)
  (`DeckTrivialOnH1`, e.g. from `deckTrivial_of_bezout`), the
  pushforward of every cover 1-cycle lands in a seam coset
  (`push1_mem_seamCoset_of_deckTrivial` — proof: `τ(p v) = v + σv` is a
  boundary).  Hence a cover cycle of weight `< m` whose pushforward is
  not a base boundary refutes `SeamCosetFloor m` outright
  (`not_seamCosetFloor_of_light_cover_cycle`): **the safe floor
  inherits the cover's safe-sector failure at no weight cost**
  (`d_safe ≤ d̃_safe`).  This is the converse direction to
  `safeFloor_of_seamCosetFloor`.
-/

import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `coverComplex`/`baseComplex` projections unfold deep
-- `Prod`/`ZMod` instance chains, exactly as in `BBCover.lean`.
set_option maxRecDepth 4096

/-! ## The augmentation is multiplicative on convolutions -/

section Augmentation

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- The augmentation of a convolution is the product of augmentations:
`∑ (a ⋆ b) = (∑ a) · (∑ b)`. -/
lemma sum_conv (a b : G → ZMod 2) :
    ∑ g : G, conv a b g = (∑ g : G, a g) * (∑ g : G, b g) := by
  simp only [conv_apply]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight h) b

omit [AddCommGroup G] in
/-- Over `ZMod 2`, the sum of a chain is its support parity: the cast of
the support count equals `∑ v`. -/
lemma natCast_card_support (v : G → ZMod 2) :
    (((Finset.univ.filter fun g => v g ≠ 0).card : ℕ) : ZMod 2)
      = ∑ g : G, v g := by
  have hval : ∀ g : G, v g ≠ 0 → v g = 1 := by
    intro g
    generalize v g = x
    decide +revert
  rw [← Finset.sum_filter_ne_zero Finset.univ, Finset.card_eq_sum_ones,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Nat.cast_one]
  exact (hval g (Finset.mem_filter.mp hg).2).symm

end Augmentation

/-! ## Parity (L1): cycles of odd-weight BB complexes have even weight -/

section Parity

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- **Parity (L1).** If both polynomials have odd weight
(`∑ A = ∑ B = 1` in `ZMod 2`), every 1-cycle of the BB complex has even
support: the augmentation applied to `B⋆v_L + A⋆v_R = 0` gives
`∑ v_L = ∑ v_R`, so `∑ v = 0`. -/
theorem cycle_support_even (A B : G → ZMod 2)
    (hA : ∑ g : G, A g = 1) (hB : ∑ g : G, B g = 1)
    {v : G × Fin 2 → ZMod 2} (hv : bbBoundary1Fn A B v = 0) :
    Even ((Finset.univ.filter fun p : G × Fin 2 => v p ≠ 0).card) := by
  classical
  -- the total sum of the cycle vanishes
  have hsum : ∑ p : G × Fin 2, v p = 0 := by
    have h0 : ∑ g : G, bbBoundary1Fn A B v g = 0 := by
      rw [hv]; exact Finset.sum_const_zero
    have hexp : ∑ g : G, bbBoundary1Fn A B v g
        = (∑ g : G, v (g, 0)) + (∑ g : G, v (g, 1)) := by
      unfold bbBoundary1Fn
      rw [Finset.sum_add_distrib, sum_conv, sum_conv, hA, hB, one_mul,
        one_mul]
      rfl
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [Fin.sum_univ_two]
    rw [hexp] at h0
    exact h0
  -- support parity = total sum = 0
  have hcast : (((Finset.univ.filter fun p : G × Fin 2 => v p ≠ 0).card : ℕ)
      : ZMod 2) = 0 := by
    rw [natCast_card_support (G := G × Fin 2) v]
    exact hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

end Parity

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## Parity instantiated on the cover bundle -/

/-- The cover polynomials have the same augmentation as their descents
(fiber summation preserves totals). -/
lemma sum_cover_eq_sum_base (v : G → ZMod 2) :
    ∑ g : G, v g = ∑ h : H, fiberSumFn (⇑D.proj) v h := by
  classical
  unfold fiberSumFn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (D.proj g) (fun _ => v g)]
  simp

/-- Parity for base 1-cycles, from the odd-weight hypothesis on the base
polynomials. -/
theorem base_cycle_weight_even
    (hA : ∑ h : H, D.Ab h = 1) (hB : ∑ h : H, D.Bb h = 1)
    {u : H × Fin 2 → ZMod 2} (hu : u ∈ D.baseComplex.cycles) :
    Even (D.baseComplex.chainWeight u) := by
  rw [D.baseComplex_chainWeight_eq]
  exact cycle_support_even D.Ab D.Bb hA hB hu

/-- Parity for cover 1-cycles: the cover polynomial augmentations descend
(`push_A`, `push_B`), so the same odd-weight hypotheses suffice. -/
theorem cover_cycle_weight_even
    (hA : ∑ h : H, D.Ab h = 1) (hB : ∑ h : H, D.Bb h = 1)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles) :
    Even (D.coverComplex.chainWeight v) := by
  have hAc : ∑ g : G, D.Ac g = 1 := by
    rw [D.sum_cover_eq_sum_base D.Ac]
    rw [show fiberSumFn (⇑D.proj) D.Ac = D.Ab from D.push_A]
    exact hA
  have hBc : ∑ g : G, D.Bc g = 1 := by
    rw [D.sum_cover_eq_sum_base D.Bc]
    rw [show fiberSumFn (⇑D.proj) D.Bc = D.Bb from D.push_B]
    exact hB
  rw [D.coverComplex_chainWeight_eq]
  exact cycle_support_even D.Ac D.Bc hAc hBc hv

/-! ## The seam transfer identity (L0, reverse direction) -/

/-- **`τ(seamC ζ) = liftStab ζ`** for a base 2-cycle `ζ`: the pullback of
the seam-crossing chain is the lifted stabilizer.  (Same chase as
`seamC_mem_cycles`, keeping the pullback identity.) -/
theorem pull1_seamC {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    D.pull1 (D.seamC ζ) = D.liftStab ζ := by
  -- the lifted stabilizer pushes to `∂₂ ζ = 0`, so it is a pullback
  have hpush : D.push1 (D.liftStab ζ) = 0 := by
    rw [D.push1_liftStab]; exact hζ
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hpush
  -- its sheet 0 recovers `u`, and equals `seamN ζ` by definition
  have hseamN : D.seamN ζ = u := by
    change D.sheet0 (D.liftStab ζ) = u
    rw [hu, D.sheet0_pull1]
  -- char 2: `seamN ζ + seamC ζ = ∂₂ ζ = 0` forces `seamC ζ = seamN ζ`
  have hseamC : D.seamC ζ = u := by
    have hkey : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    funext j
    have hsum := D.seamN_add_seamC ζ j
    rw [hseamN, hζ, Pi.zero_apply] at hsum
    exact hkey _ _ hsum
  rw [hseamC, ← hu]

/-- Easy direction of L0: every seam-coset element pulls back to a cover
boundary. -/
theorem pull1_seamCoset_mem_boundaries {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) (f : H → ZMod 2) :
    D.pull1 (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f)
      ∈ D.coverComplex.boundaries := by
  rw [map_add, D.pull1_seamC hζ]
  exact Submodule.add_mem _ (D.liftStab_mem_boundaries ζ)
    (D.pull1_mem_boundaries ⟨f, rfl⟩)

/-! ## The seam transfer kernel (L0, forward chase) -/

/-- The deck orbit map on `C0`/`C2` indices has no fixed points. -/
lemma deckSigma0_ne : ∀ g : G, g + D.deckS ≠ g := by
  intro g hg
  apply D.deckS_ne_zero
  have h : g + D.deckS = g + 0 := by rw [add_zero]; exact hg
  exact add_left_cancel h

/-- Sheet-1 restriction also inverts the pullback (deck partner of
`sheet0_pull1`). -/
lemma sheet1_pull1 (u : H × Fin 2 → ZMod 2) :
    D.sheet1 (D.pull1 u) = u := by
  funext q
  change u (Prod.map ⇑D.proj id (D.deckSigma1 (D.sec1 q))) = u q
  have hproj : Prod.map ⇑D.proj id (D.deckSigma1 (D.sec1 q))
      = Prod.map ⇑D.proj id (D.sec1 q) := by
    change (D.proj ((D.sec1 q).1 + D.deckS), (D.sec1 q).2)
      = (D.proj (D.sec1 q).1, (D.sec1 q).2)
    rw [D.proj_add_deckS]
  rw [hproj, D.proj_prodMap_sec1 q]

/-- Fiber pair formula for the 0/2-chain pushforward:
`(p₀ z)(proj g) = z g + z (g + deckS)`. -/
lemma push0_pair (z : G → ZMod 2) (g : G) :
    fiberSumFn (⇑D.proj) z (D.proj g) = z g + z (g + D.deckS) :=
  fiberSumFn_pair D.deckSigma0_ne D.proj_fiber z g

/-- The two 2-chain sheets sum to the pushforward. -/
lemma sheetC2_0_add_sheetC2_1 (z : G → ZMod 2) (h : H) :
    D.sheetC2_0 z h + D.sheetC2_1 z h = fiberSumFn (⇑D.proj) z h := by
  have hp := D.push0_pair z (D.sec h)
  rw [D.proj_sec h] at hp
  exact hp.symm

/-- **The seam transfer kernel, forward chase**: a base 1-chain whose
pullback is a cover boundary lies in a seam coset.  Descend the boundary
witness `c` through the sheet decomposition `liftC2_decomp`: with
`ξ₀, ξ₁` its sheets and `ζ = ξ₀ + ξ₁`, taking `sheet1` of
`τ w = ∂₂ᶜ c = liftStab ξ₀ + σ(liftStab ξ₁)` gives
`w = seamC ξ₀ + seamN ξ₁ = seamC ζ + ∂₂ᵇ ξ₁` (char 2). -/
theorem exists_seamCoset_of_pull1_mem_boundaries {w : H × Fin 2 → ZMod 2}
    (hbd : D.pull1 w ∈ D.coverComplex.boundaries) :
    ∃ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 ∧
      ∃ f : H → ZMod 2, w = D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f := by
  obtain ⟨c, hc⟩ := hbd
  -- `hc : bbBoundary2Fn Ac Bc c = pull1 w` (unfold the boundary map)
  have hc' : bbBoundary2Fn D.Ac D.Bc c = D.pull1 w := hc
  set ξ₀ : H → ZMod 2 := D.sheetC2_0 c with hξ₀
  set ξ₁ : H → ZMod 2 := D.sheetC2_1 c with hξ₁
  refine ⟨ξ₀ + ξ₁, ?_, ξ₁, ?_⟩
  · -- `ξ₀ + ξ₁ = p₀ c` is a base 2-cycle: `∂₂ᵇ (p₀ c) = p₁ (∂₂ᶜ c)
    --  = p₁ (τ w) = 0`
    have hsum : ξ₀ + ξ₁ = fiberSumFn (⇑D.proj) c := by
      funext h
      rw [Pi.add_apply]
      exact D.sheetC2_0_add_sheetC2_1 c h
    have hcomm := D.push_boundary2_comm c
    have hzero : D.push1 (D.pull1 w) = 0 := D.push1_pull1_eq_zero w
    have hpush2 : D.baseComplex.boundary2 (D.push0 c) = 0 := by
      rw [← hcomm]
      change D.push1 (bbBoundary2Fn D.Ac D.Bc c) = 0
      rw [hc']
      exact hzero
    rw [hsum]
    exact hpush2
  · -- decompose the boundary witness sheet-wise and take `sheet1`
    have hdec := D.liftC2_decomp c
    have hboundary : bbBoundary2Fn D.Ac D.Bc c
        = D.liftStab ξ₀ + D.deckShift1 (D.liftStab ξ₁) := by
      conv_lhs => rw [hdec]
      rw [bbBoundary2Fn_add]
      rw [D.liftStab_deckShift ξ₁]
      rfl
    -- apply `sheet1` to both sides of `τ w = liftStab ξ₀ + σ (liftStab ξ₁)`
    have hs1 : D.sheet1 (D.pull1 w)
        = D.sheet1 (D.liftStab ξ₀) + D.sheet1 (D.deckShift1 (D.liftStab ξ₁)) := by
      rw [← hc', hboundary, D.sheet1_add]
    rw [D.sheet1_pull1, D.sheet1_deckShift1] at hs1
    -- `sheet1 (liftStab ξ₀) = seamC ξ₀`, `sheet0 (liftStab ξ₁) = seamN ξ₁`
    have hs1' : w = D.seamC ξ₀ + D.seamN ξ₁ := hs1
    -- char 2: `seamN ξ₁ = ∂₂ᵇ ξ₁ + seamC ξ₁`
    have hseamN : D.seamN ξ₁ = bbBoundary2Fn D.Ab D.Bb ξ₁ + D.seamC ξ₁ := by
      have hkey : ∀ a b c : ZMod 2, a + b = c → a = c + b := by decide
      funext j
      exact hkey _ _ _ (D.seamN_add_seamC ξ₁ j)
    rw [hs1', hseamN, D.seamC_add]
    abel

/-- **The seam transfer kernel (L0, chain form)**: a base 1-chain pulls
back to a cover boundary **iff** it lies in a seam coset.  This is the
connecting-map slot `im δ₂ = ker τ₁` of the transfer LES at chain level
(the H₁-quotient packaging of the reverse slot is
`BBTransferH1.ker_pushH1_eq_range_pullH1`). -/
theorem pull1_mem_boundaries_iff_seamCoset (w : H × Fin 2 → ZMod 2) :
    D.pull1 w ∈ D.coverComplex.boundaries
      ↔ ∃ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 ∧
          ∃ f : H → ZMod 2, w = D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f := by
  constructor
  · exact D.exists_seamCoset_of_pull1_mem_boundaries
  · rintro ⟨ζ, hζ, f, rfl⟩
    exact D.pull1_seamCoset_mem_boundaries hζ f

/-! ## The pushforward bound (T2) -/

/-- **T2, membership form**: under the deck homotopy (R), the pushforward
of every cover 1-cycle lies in a seam coset — `τ(p v) = v + σv` is a
cover boundary, so L0 applies. -/
theorem push1_mem_seamCoset_of_deckTrivial (hR : D.DeckTrivialOnH1)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles) :
    ∃ ζ : H → ZMod 2, bbBoundary2Fn D.Ab D.Bb ζ = 0 ∧
      ∃ f : H → ZMod 2,
        D.push1 v = D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f := by
  apply D.exists_seamCoset_of_pull1_mem_boundaries
  rw [D.pull1_push1 v]
  exact hR v hv

/-- **T2, weight form (the wall inheritance)**: a cover 1-cycle of weight
`< m` whose pushforward is not a base boundary refutes
`SeamCosetFloor m` — the safe floor inherits the cover's safe-sector
failure at no weight cost (`d_safe ≤ d̃_safe`).  Converse direction to
`safeFloor_of_seamCosetFloor`. -/
theorem not_seamCosetFloor_of_light_cover_cycle (hR : D.DeckTrivialOnH1)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles)
    (hpush : D.push1 v ∉ D.baseComplex.boundaries)
    {m : ℕ} (hm : D.coverComplex.chainWeight v < m) :
    ¬ D.SeamCosetFloor m := by
  intro hSF
  obtain ⟨ζ, hζ, f, heq⟩ := D.push1_mem_seamCoset_of_deckTrivial hR hv
  have hfloor := hSF ζ hζ f (heq ▸ hpush)
  rw [← heq] at hfloor
  exact absurd (le_trans hfloor (D.chainWeight_push_le v))
    (not_le.mpr hm)

/-! ## The deficit wall: odd-step upgrades of the floors -/

/-- Every seam-coset element is a base 1-cycle. -/
lemma seamCoset_mem_cycles {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) (f : H → ZMod 2) :
    D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f ∈ D.baseComplex.cycles :=
  Submodule.add_mem _ (D.seamC_mem_cycles hζ)
    (D.baseComplex.boundaries_le_cycles ⟨f, rfl⟩)

/-- **The deficit wall (seam-coset form).** Under the parity hypothesis,
the seam-coset floor at `m − 1` upgrades to `m` for even `m`: every
coset element is a cycle, hence of even weight, so weight `≥ m − 1`
forces weight `≥ m`.  Contrapositive: an SF-failing cell at even target
`m` already fails at `m − 1`, i.e. **the maximal failing value is
`m − 2`.** -/
theorem seamCosetFloor_of_even_of_pred
    (hA : ∑ h : H, D.Ab h = 1) (hB : ∑ h : H, D.Bb h = 1)
    {m : ℕ} (hm : Even m)
    (h : D.SeamCosetFloor (m - 1)) : D.SeamCosetFloor m := by
  intro ζ hζ f hnb
  have hfloor := h ζ hζ f hnb
  have heven : Even (D.baseComplex.chainWeight
      (D.seamC ζ + bbBoundary2Fn D.Ab D.Bb f)) :=
    D.base_cycle_weight_even hA hB (D.seamCoset_mem_cycles hζ f)
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := heven
  omega

/-- **The deficit wall (safe-floor form).** Same upgrade for the
cover-side `SafeFloor`: safe-sector cover cycles have even weight. -/
theorem safeFloor_of_even_of_pred
    (hA : ∑ h : H, D.Ab h = 1) (hB : ∑ h : H, D.Bb h = 1)
    {m : ℕ} (hm : Even m)
    (h : D.SafeFloor (m - 1)) : D.SafeFloor m := by
  intro v hv hpush
  have hfloor := h v hv hpush
  have heven : Even (D.coverComplex.chainWeight v) :=
    D.cover_cycle_weight_even hA hB hv
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := heven
  omega

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum

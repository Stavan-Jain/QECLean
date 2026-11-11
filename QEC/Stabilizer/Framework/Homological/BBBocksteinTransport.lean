import QEC.Stabilizer.Framework.Homological.BBTransferH1
import QEC.Stabilizer.Framework.Homological.BBDeficitWall
import QEC.Stabilizer.Framework.Homological.BBConvRing
import QEC.Stabilizer.Framework.Homological.BBEpsFreeGroupAlgebra

/-!
# The Bockstein-vanishing criterion from an order-four lift of the deck

Let `D : XDoubleCoverData G H` be a free double cover of bivariate bicycle
codes with cover polynomials `A`, `B`, pushforward `p`, pullback `τ` and deck
translation `σ`, and write `ε = 1 + x^σ` for the element `deckPoly` of `𝔽₂[G]`,
so that convolution by `ε` is `1 + σ`. The criterion `BocksteinVanishes`
(`ker τ_* ≤ range p_*` on `H₁`) is the hypothesis under which
`dim (range ε_*) = k̃ - k` (`finrank_range_epsH1_eq`). This file proves it
whenever the deck translation lifts to an element of order four in a further
double cover of `G`, and in particular for the cover groups
`ZMod (2 * n) × ZMod m` with deck translation `(n, t)`.

## From the element form to the criterion

`BocksteinElementForm` is the following statement in `𝔽₂[G]`: whenever
`A ⋆ z = ε ⋆ a` and `B ⋆ z = ε ⋆ b`, there are `r`, `s` with
`A ⋆ b + B ⋆ a = ε ⋆ (A ⋆ r + B ⋆ s)`.

* `pull0_eq_conv_deckPoly_liftC2`: `τ u = ε ⋆ liftC2 u` on chains indexed by
  `H`; `push0_eq_zero_iff_exists_conv_deckPoly`: the kernel of `p` on chains
  indexed by `G` consists of the multiples of `ε`.
* `conv_Ac_liftC2_seamC`, `conv_Bc_liftC2_seamC`: for a base 2-cycle `ζ`, the
  two halves of `τ (seamC ζ) = liftStab ζ` read `A ⋆ liftC2 ζ = ε ⋆ ã` and
  `B ⋆ liftC2 ζ = ε ⋆ b̃`, where `ã`, `b̃` are the lifts of the halves of
  `seamC ζ`.
* `exists_cycle_push_eq_seamC`: under the element form, `seamC ζ` is the
  pushforward of the cover 1-cycle `(ã + ε ⋆ s | b̃ + ε ⋆ r)`.
* `bocksteinVanishes_of_elementForm`: the element form implies
  `BocksteinVanishes`, because the kernel of `τ_*` consists of the classes of
  the chains `seamC ζ`.

## The element form from an order-four lift

* `one_add_single_dvd_of_mapDomainRingHom_eq_zero`: for a surjective
  homomorphism `q : Ĝ →+ G` whose fibers are the orbits of a nonzero `c`, the
  kernel of the ring homomorphism `𝔽₂[q] : 𝔽₂[Ĝ] → 𝔽₂[G]` consists of the
  multiples of `1 + x^c`.
* `elementForm_of_orderFourLift`: if `q : Ĝ →+ G` is surjective and `ŝ : Ĝ`
  has order four, with `q ŝ = σ` and `ker q = {0, ŝ + ŝ}`, the element form
  holds. With `ε̂ = 1 + x^ŝ`, the ring homomorphism `𝔽₂[q]` maps `ε̂` to `ε`
  and has kernel `(ε̂ ^ 2)`, the annihilator of `ε̂` is `(ε̂ ^ 3)`
  (`BBEpsFree.epsFree_one_add_single_of_addOrderOf`), and
  `BocksteinLift.bockstein_element_form_of_surjective` applies.
* `bocksteinVanishes_of_orderFourLift`,
  `finrank_range_epsH1_eq_of_orderFourLift`: the criterion and the rank
  equality under the same hypotheses.
* `elementForm_of_zmod_double`, `bocksteinVanishes_of_zmod_double`,
  `finrank_range_epsH1_eq_of_zmod_double`: the case of a cover group
  `ZMod (2 * n) × ZMod m` with deck translation `(n, t)`, `t + t = 0`, where the
  lift is the reduction `ZMod (4 * n) × ZMod m → ZMod (2 * n) × ZMod m` and
  `ŝ = (n, t)`. The `_right` versions exchange the two factors.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped Homology

/-! ## Assembling a 1-chain from its halves -/

/-- The 1-chain with left half `vL` and right half `vR`. -/
def joinHalves {G : Type} (vL vR : G → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun p => if p.2 = 0 then vL p.1 else vR p.1

@[simp] lemma leftHalf_joinHalves {G : Type} (vL vR : G → ZMod 2) :
    leftHalf (joinHalves vL vR) = vL := rfl

@[simp] lemma rightHalf_joinHalves {G : Type} (vL vR : G → ZMod 2) :
    rightHalf (joinHalves vL vR) = vR := rfl

/-! ## The group algebra and fiber summation -/

/-- In `𝔽₂[G]`, `(1 + x^σ) ^ 2 = 1 + x^(σ + σ)`. -/
lemma one_add_single_sq {G : Type*} [AddCommGroup G] (σ : G) :
    (1 + AddMonoidAlgebra.single σ (1 : ZMod 2)) ^ 2
      = 1 + AddMonoidAlgebra.single (σ + σ) 1 := by
  have h2 : (2 : AddMonoidAlgebra (ZMod 2) G) = 0 :=
    BBEpsFree.two_eq_zero_of_algebra _ (by decide : (2 : ZMod 2) = 0)
  rw [add_sq, h2, zero_mul, zero_mul, add_zero, one_pow, BBEpsFree.single_pow_one, two_nsmul]

section GroupAlgebra

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- `convEquiv` sends `1 + x^σ` to the chain `δ_0 + δ_σ`. -/
lemma convEquiv_one_add_single (σ : G) :
    convEquiv (1 + AddMonoidAlgebra.single σ (1 : ZMod 2))
      = Pi.single (0 : G) 1 + Pi.single σ 1 := by
  rw [map_add, AddMonoidAlgebra.one_def, convEquiv_single, convEquiv_single]

/-- `convEquiv` carries the ring homomorphism `𝔽₂[q]` induced by a group
homomorphism `q` to fiber summation along `q`. -/
lemma convEquiv_mapDomainRingHom {Ghat : Type} [Fintype Ghat] [AddCommGroup Ghat]
    (q : Ghat →+ G) (x : AddMonoidAlgebra (ZMod 2) Ghat) :
    convEquiv (AddMonoidAlgebra.mapDomainRingHom (ZMod 2) q x)
      = fiberSumFn ⇑q (convEquiv x) := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero (fiberSum ⇑q)).symm
  | add f g hf hg => rw [map_add, map_add, map_add, fiberSumFn_add, hf, hg]
  | single g c =>
    change convEquiv (AddMonoidAlgebra.mapDomain ⇑q _) = _
    rw [AddMonoidAlgebra.mapDomain_single, convEquiv_single, convEquiv_single, fiberSumFn_single]

end GroupAlgebra

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The transfer maps on chains indexed by the group -/

/-- `τ ∘ p = 1 + σ` on chains indexed by `G`: `τ (p w) = w + σ w`. -/
theorem pull0_push0 (w : G → ZMod 2) :
    D.pull0 (D.push0 w) = w + D.deckShift0 w :=
  funext (D.push0_pair w)

/-- `p ∘ τ = 0` on chains indexed by `H`. -/
theorem push0_pull0_eq_zero (u : H → ZMod 2) :
    D.push0 (D.pull0 u) = 0 :=
  fiberSumFn_pullback D.deckSigma0_ne D.proj_fiber u

/-- `ker p = im τ` on chains indexed by `G`. -/
theorem push0_eq_zero_iff (w : G → ZMod 2) :
    D.push0 w = 0 ↔ ∃ u : H → ZMod 2, w = D.pull0 u :=
  fiberSumFn_eq_zero_iff D.deckSigma0_ne D.proj_fiber D.proj_sec w

/-- `τ u = ε ⋆ liftC2 u`: the pullback of a base chain is `deckPoly` convolved
with its lift to sheet 0. -/
theorem pull0_eq_conv_deckPoly_liftC2 (u : H → ZMod 2) :
    D.pull0 u = D.deckPoly ⋆ D.liftC2 u := by
  rw [D.conv_deckPoly_eq, ← D.pull0_push0, push0_apply, D.push0_liftC2]

/-- `p (ε ⋆ w) = 0`: the pushforward kills the multiples of `deckPoly`. -/
theorem push0_conv_deckPoly_eq_zero (w : G → ZMod 2) :
    D.push0 (D.deckPoly ⋆ w) = 0 := by
  rw [D.conv_deckPoly_eq, ← D.pull0_push0, D.push0_pull0_eq_zero]

/-- The kernel of `p` on chains indexed by `G` consists of the multiples of
`deckPoly`. -/
theorem push0_eq_zero_iff_exists_conv_deckPoly (w : G → ZMod 2) :
    D.push0 w = 0 ↔ ∃ u : G → ZMod 2, w = D.deckPoly ⋆ u := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := (D.push0_eq_zero_iff w).mp h
    exact ⟨_, D.pull0_eq_conv_deckPoly_liftC2 u⟩
  · rintro ⟨u, rfl⟩
    exact D.push0_conv_deckPoly_eq_zero u

/-! ## The group algebras of a double cover of groups -/

/-- A surjective homomorphism `q : G →+ H` whose fibers are the orbits
`{g, g + c}` of a nonzero `c`, as a double cover with all four polynomials zero.
It makes the transfer maps `push0`, `pull0` and `liftC2` of `q` available. -/
noncomputable def ofSurjective (q : G →+ H) (c : G) (hc : c ≠ 0)
    (hfiber : ∀ g g' : G, q g' = q g ↔ g' = g ∨ g' = g + c)
    (hsurj : Function.Surjective ⇑q) : XDoubleCoverData G H where
  proj := q
  deckS := c
  sec := Function.surjInv hsurj
  Ac := 0
  Bc := 0
  Ab := 0
  Bb := 0
  deckS_ne_zero := hc
  proj_fiber := hfiber
  proj_sec := Function.surjInv_eq hsurj
  push_A := map_zero (fiberSum ⇑q)
  push_B := map_zero (fiberSum ⇑q)

end XDoubleCoverData

/-- For a surjective homomorphism `q : Ĝ →+ G` whose fibers are the orbits
`{g, g + c}` of a nonzero `c`, the kernel of the ring homomorphism
`𝔽₂[q] : 𝔽₂[Ĝ] → 𝔽₂[G]` consists of the multiples of `1 + x^c`. -/
theorem one_add_single_dvd_of_mapDomainRingHom_eq_zero {Ghat G : Type} [Finite Ghat]
    [AddCommGroup Ghat] [AddCommGroup G] (q : Ghat →+ G) (hsurj : Function.Surjective ⇑q)
    {c : Ghat} (hc : c ≠ 0) (hfiber : ∀ g g' : Ghat, q g' = q g ↔ g' = g ∨ g' = g + c)
    {x : AddMonoidAlgebra (ZMod 2) Ghat}
    (hx : AddMonoidAlgebra.mapDomainRingHom (ZMod 2) q x = 0) :
    1 + AddMonoidAlgebra.single c (1 : ZMod 2) ∣ x := by
  classical
  have := Finite.of_surjective _ hsurj
  cases nonempty_fintype Ghat
  cases nonempty_fintype G
  obtain ⟨u, hu⟩ := ((XDoubleCoverData.ofSurjective q c hc hfiber
    hsurj).push0_eq_zero_iff_exists_conv_deckPoly (convEquiv x)).mp
    ((convEquiv_mapDomainRingHom q x).symm.trans (by rw [hx, map_zero]))
  refine ⟨convEquiv.symm u, convEquiv.injective ?_⟩
  rw [convEquiv_mul, convEquiv_one_add_single, LinearEquiv.apply_symm_apply]
  exact hu

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The transfer maps on the halves of a 1-chain -/

/-- `p` acts on the left half of a 1-chain as `p` on chains indexed by `G`. -/
lemma leftHalf_push1 (v : G × Fin 2 → ZMod 2) :
    leftHalf (D.push1 v) = D.push0 (leftHalf v) :=
  leftHalf_fiberSumFn_prodMap D.proj v

/-- `p` acts on the right half of a 1-chain as `p` on chains indexed by `G`. -/
lemma rightHalf_push1 (v : G × Fin 2 → ZMod 2) :
    rightHalf (D.push1 v) = D.push0 (rightHalf v) :=
  rightHalf_fiberSumFn_prodMap D.proj v

/-- `τ` acts on the left half of a 1-chain as `τ` on chains indexed by `H`. -/
lemma leftHalf_pull1 (u : H × Fin 2 → ZMod 2) :
    leftHalf (D.pull1 u) = D.pull0 (leftHalf u) := rfl

/-- `τ` acts on the right half of a 1-chain as `τ` on chains indexed by `H`. -/
lemma rightHalf_pull1 (u : H × Fin 2 → ZMod 2) :
    rightHalf (D.pull1 u) = D.pull0 (rightHalf u) := rfl

/-! ## The seam chain of a base 2-cycle -/

/-- For a base 2-cycle `ζ`, `A ⋆ liftC2 ζ = ε ⋆ liftC2 (seamC ζ)_L`: the left
half of `τ (seamC ζ) = liftStab ζ`, with `τ` written as `ε ⋆ liftC2`. -/
theorem conv_Ac_liftC2_seamC {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    D.Ac ⋆ D.liftC2 ζ = D.deckPoly ⋆ D.liftC2 (leftHalf (D.seamC ζ)) := by
  rw [← D.pull0_eq_conv_deckPoly_liftC2, ← D.leftHalf_pull1, D.pull1_seamC hζ]
  rfl

/-- For a base 2-cycle `ζ`, `B ⋆ liftC2 ζ = ε ⋆ liftC2 (seamC ζ)_R`: the right
half of `τ (seamC ζ) = liftStab ζ`. -/
theorem conv_Bc_liftC2_seamC {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    D.Bc ⋆ D.liftC2 ζ = D.deckPoly ⋆ D.liftC2 (rightHalf (D.seamC ζ)) := by
  rw [← D.pull0_eq_conv_deckPoly_liftC2, ← D.rightHalf_pull1, D.pull1_seamC hζ]
  rfl

/-! ## The element form and the criterion -/

/-- The Bockstein element form of a double cover, with `A`, `B` the cover
polynomials and `ε = deckPoly`: whenever `A ⋆ z = ε ⋆ a` and `B ⋆ z = ε ⋆ b`,
the chain `A ⋆ b + B ⋆ a` is `ε ⋆ (A ⋆ r + B ⋆ s)` for some `r`, `s`. It says
that the composite of the two connecting maps `H₂ → H₁ → H₀` of the base
vanishes on representatives. -/
def BocksteinElementForm : Prop :=
  ∀ z a b : G → ZMod 2,
    D.Ac ⋆ z = D.deckPoly ⋆ a →
    D.Bc ⋆ z = D.deckPoly ⋆ b →
    ∃ r s : G → ZMod 2,
      D.Ac ⋆ b + D.Bc ⋆ a = D.deckPoly ⋆ (D.Ac ⋆ r + D.Bc ⋆ s)

/-- Under the element form, the seam chain `seamC ζ` of a base 2-cycle `ζ` is
the pushforward of a cover 1-cycle. With `ã`, `b̃` the lifts of the two halves
of `seamC ζ` and `r`, `s` the witnesses of the element form, the cycle is
`(ã + ε ⋆ s | b̃ + ε ⋆ r)`; the corrections vanish under `p`. -/
theorem exists_cycle_push_eq_seamC (hEF : D.BocksteinElementForm)
    {ζ : H → ZMod 2} (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    ∃ v ∈ D.coverComplex.cycles, D.push1 v = D.seamC ζ := by
  obtain ⟨r, s, hrs⟩ := hEF _ _ _ (D.conv_Ac_liftC2_seamC hζ) (D.conv_Bc_liftC2_seamC hζ)
  refine ⟨joinHalves (D.liftC2 (leftHalf (D.seamC ζ)) + D.deckPoly ⋆ s)
    (D.liftC2 (rightHalf (D.seamC ζ)) + D.deckPoly ⋆ r), ?_, halves_ext_iff.mpr ⟨?_, ?_⟩⟩
  · change bbBoundary1Fn D.Ac D.Bc _ = 0
    rw [bbBoundary1Fn_eq, leftHalf_joinHalves, rightHalf_joinHalves, conv_add_right,
      conv_add_right, ← conv_assoc D.Bc, ← conv_assoc D.Ac, conv_comm D.Bc D.deckPoly,
      conv_comm D.Ac D.deckPoly, conv_assoc, conv_assoc, add_add_add_comm,
      add_comm (D.Bc ⋆ D.liftC2 _), hrs, conv_add_right, ZModModule.add_add_add_cancel,
      ZModModule.add_self]
  · rw [D.leftHalf_push1, leftHalf_joinHalves, map_add, D.push0_conv_deckPoly_eq_zero, add_zero,
      push0_apply, D.push0_liftC2]
  · rw [D.rightHalf_push1, rightHalf_joinHalves, map_add, D.push0_conv_deckPoly_eq_zero,
      add_zero, push0_apply, D.push0_liftC2]

/-- The element form implies `BocksteinVanishes`: a class in the kernel of `τ_*`
is represented by `seamC ζ` for a base 2-cycle `ζ`
(`exists_seamCoset_of_pull1_mem_boundaries`), which is the pushforward of a
cover cycle (`exists_cycle_push_eq_seamC`). -/
theorem bocksteinVanishes_of_elementForm (hEF : D.BocksteinElementForm) :
    D.BocksteinVanishes := by
  intro x hx
  obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hbd : D.pull1Cycles ⟨u, hu⟩ ∈ D.coverComplex.boundarySubmoduleInCycles :=
    (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx)
  obtain ⟨ζ, hζ, f, rfl⟩ := D.exists_seamCoset_of_pull1_mem_boundaries hbd
  obtain ⟨v, hv, hpush⟩ := D.exists_cycle_push_eq_seamC hEF hζ
  refine ⟨Submodule.Quotient.mk ⟨v, hv⟩, ((Submodule.Quotient.eq _).mpr ?_).symm⟩
  change ((⟨_, hu⟩ - D.push1Cycles ⟨v, hv⟩ : D.baseComplex.cycles) :
      D.baseComplex.C1 → ZMod 2) ∈ D.baseComplex.boundaries
  exact ⟨f, eq_sub_of_add_eq' (congrArg (· + _) hpush)⟩

/-! ## The element form from an order-four lift of the deck -/

/-- If the deck translation `σ = deckS` lifts to an element of order four, the
element form holds: it suffices that there are a surjective homomorphism
`q : Ĝ →+ G` and `ŝ : Ĝ` of order four with `q ŝ = σ` and `ker q = {0, ŝ + ŝ}`.
Put `ε̂ = 1 + x^ŝ`. The ring homomorphism `𝔽₂[q]` is surjective, maps `ε̂` to
`ε` and has kernel `(ε̂ ^ 2)`, and the annihilator of `ε̂` in `𝔽₂[Ĝ]` is
`(ε̂ ^ 3)`, so `BocksteinLift.bockstein_element_form_of_surjective` applies. -/
theorem elementForm_of_orderFourLift {Ghat : Type}
    [Finite Ghat] [AddCommGroup Ghat]
    (q : Ghat →+ G) (shat : Ghat)
    (horder : addOrderOf shat = 4)
    (hsurj : Function.Surjective ⇑q)
    (hshat : q shat = D.deckS)
    (hker : ∀ x : Ghat, q x = 0 ↔ x = 0 ∨ x = shat + shat) :
    D.BocksteinElementForm := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hc : shat + shat ≠ 0 := fun h =>
    absurd (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero ((two_nsmul shat).trans h)) (by decide)
  have hfiber : ∀ g g' : Ghat, q g' = q g ↔ g' = g ∨ g' = g + (shat + shat) := fun g g' => by
    rw [← sub_eq_zero, ← map_sub, hker, sub_eq_zero, sub_eq_iff_eq_add']
  have hε : AddMonoidAlgebra.mapDomainRingHom (ZMod 2) q
      (1 + AddMonoidAlgebra.single shat 1) = 1 + AddMonoidAlgebra.single D.deckS 1 := by
    rw [map_add, map_one, ← hshat]
    exact congrArg _ AddMonoidAlgebra.mapDomain_single
  have hε' : (1 + AddMonoidAlgebra.single D.deckS (1 : ZMod 2)) ^ 2 = 0 := by
    rw [one_add_single_sq, D.deckS_add_deckS, ← AddMonoidAlgebra.one_def, one_add_one_eq_two]
    exact BBEpsFree.two_eq_zero_of_algebra _ h2
  intro z a b hAz hBz
  obtain ⟨A, hA⟩ := convEquiv.surjective D.Ac
  obtain ⟨B, hB⟩ := convEquiv.surjective D.Bc
  obtain ⟨z, rfl⟩ := convEquiv.surjective z
  obtain ⟨a, rfl⟩ := convEquiv.surjective a
  obtain ⟨b, rfl⟩ := convEquiv.surjective b
  have hD : D.deckPoly = convEquiv (1 + AddMonoidAlgebra.single D.deckS 1) :=
    (convEquiv_one_add_single D.deckS).symm
  rw [← hA, hD, ← convEquiv_mul, ← convEquiv_mul] at hAz
  rw [← hB, hD, ← convEquiv_mul, ← convEquiv_mul] at hBz
  obtain ⟨r, s, hrs⟩ := BocksteinLift.bockstein_element_form_of_surjective
    (AddMonoidAlgebra.mapDomainRingHom (ZMod 2) q) (Finsupp.mapDomain_surjective hsurj) hε hε'
    (BBEpsFree.two_eq_zero_of_algebra _ h2)
    (BBEpsFree.hann_of_epsFree (BBEpsFree.epsFree_one_add_single_of_addOrderOf h2 shat 2 horder))
    (fun x hx => one_add_single_sq shat ▸
      one_add_single_dvd_of_mapDomainRingHom_eq_zero q hsurj hc hfiber hx)
    (convEquiv.injective hAz) (convEquiv.injective hBz)
  refine ⟨convEquiv r, convEquiv s, ?_⟩
  rw [← hA, ← hB, hD]
  simp only [← convEquiv_mul, ← map_add, hrs]

/-- `BocksteinVanishes` holds when the deck translation lifts to an element of
order four, in the sense of `elementForm_of_orderFourLift`. -/
theorem bocksteinVanishes_of_orderFourLift {Ghat : Type}
    [Finite Ghat] [AddCommGroup Ghat]
    (q : Ghat →+ G) (shat : Ghat)
    (horder : addOrderOf shat = 4)
    (hsurj : Function.Surjective ⇑q)
    (hshat : q shat = D.deckS)
    (hker : ∀ x : Ghat, q x = 0 ↔ x = 0 ∨ x = shat + shat) :
    D.BocksteinVanishes :=
  D.bocksteinVanishes_of_elementForm
    (D.elementForm_of_orderFourLift q shat horder hsurj hshat hker)

/-- When the deck translation lifts to an element of order four,
`dim (range ε_*) = k̃ - k`. -/
theorem finrank_range_epsH1_eq_of_orderFourLift {Ghat : Type}
    [Finite Ghat] [AddCommGroup Ghat]
    (q : Ghat →+ G) (shat : Ghat)
    (horder : addOrderOf shat = 4)
    (hsurj : Function.Surjective ⇑q)
    (hshat : q shat = D.deckS)
    (hker : ∀ x : Ghat, q x = 0 ↔ x = 0 ∨ x = shat + shat) :
    dim₂ (LinearMap.range D.epsH1)
      = dim₂ D.coverComplex.H1 - dim₂ D.baseComplex.H1 :=
  D.finrank_range_epsH1_eq
    (D.bocksteinVanishes_of_orderFourLift q shat horder hsurj hshat hker)

end XDoubleCoverData

/-! ## Covers with a doubled cyclic factor -/

section ZModDouble

variable {n m : ℕ}

private lemma two_mul_dvd_four_mul (n : ℕ) : 2 * n ∣ 4 * n :=
  Nat.mul_dvd_mul_right (by decide) n

/-- The reduction `ZMod (4 * n) × ZMod m →+ ZMod (2 * n) × ZMod m` of the first
coordinate. -/
private def zmodDoubleProj (n m : ℕ) : ZMod (4 * n) × ZMod m →+ ZMod (2 * n) × ZMod m :=
  (ZMod.castHom (two_mul_dvd_four_mul n) (ZMod (2 * n))).toAddMonoidHom.prodMap
    (AddMonoidHom.id (ZMod m))

private lemma zmodDoubleProj_surjective : Function.Surjective (zmodDoubleProj n m) :=
  (ZMod.castHom_surjective (two_mul_dvd_four_mul n)).prodMap Function.surjective_id

private lemma zmodDoubleProj_natCast (t : ZMod m) :
    zmodDoubleProj n m ((n : ZMod (4 * n)), t) = ((n : ZMod (2 * n)), t) :=
  Prod.ext (map_natCast (ZMod.castHom (two_mul_dvd_four_mul n) (ZMod (2 * n))) n) rfl

/-- In `ZMod (4 * n) × ZMod m` with `n ≠ 0`, the element `(n, t)` has order four
when `t + t = 0`. -/
private lemma addOrderOf_natCast_prod [NeZero n] {t : ZMod m} (ht : t + t = 0) :
    addOrderOf (((n : ℕ) : ZMod (4 * n)), t) = 4 := by
  have hn := NeZero.pos n
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) (fun h => ?_) ?_
  · have h1 : ((2 * n : ℕ) : ZMod (4 * n)) = 0 := by simpa using congrArg Prod.fst h
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp h1)
    omega
  · change (4 : ℕ) • (((n : ℕ) : ZMod (4 * n)), t) = 0
    rw [Prod.smul_mk, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_self,
      show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul t, ht, smul_zero]
    rfl

/-- The kernel of the reduction `ZMod (4 * n) → ZMod (2 * n)` is
`{0, 2 * n}`. -/
private lemma castHom_four_mul_eq_zero_iff [NeZero n] (x : ZMod (4 * n)) :
    ZMod.castHom (two_mul_dvd_four_mul n) (ZMod (2 * n)) x = 0
      ↔ x = 0 ∨ x = ((n + n : ℕ) : ZMod (4 * n)) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨c, hc⟩ := h
    have hc2 : c < 2 := Nat.lt_of_mul_lt_mul_left (a := 2 * n) (by
      have := x.val_lt
      omega)
    rw [← ZMod.natCast_zmod_val x, hc]
    interval_cases c
    · exact Or.inl (by rw [mul_zero, Nat.cast_zero])
    · exact Or.inr (by rw [mul_one, two_mul])
  · rintro (rfl | rfl)
    · exact map_zero _
    · rw [map_natCast, ← two_mul, ZMod.natCast_self]

/-- The kernel of `zmodDoubleProj` is `{0, (n, t) + (n, t)}` when
`t + t = 0`. -/
private lemma zmodDoubleProj_eq_zero_iff [NeZero n] {t : ZMod m} (ht : t + t = 0)
    (x : ZMod (4 * n) × ZMod m) :
    zmodDoubleProj n m x = 0
      ↔ x = 0 ∨ x = (((n : ℕ) : ZMod (4 * n)), t) + (((n : ℕ) : ZMod (4 * n)), t) := by
  obtain ⟨x, y⟩ := x
  change (ZMod.castHom (two_mul_dvd_four_mul n) (ZMod (2 * n)) x, y) = 0 ↔ _
  rw [Prod.mk_add_mk, ht, ← Nat.cast_add, Prod.mk_eq_zero, castHom_four_mul_eq_zero_iff,
    Prod.mk_eq_zero, Prod.mk.injEq]
  tauto

end ZModDouble

namespace XDoubleCoverData

variable {H : Type} [Fintype H] [AddCommGroup H] [DecidableEq H] {n m : ℕ} [NeZero n] [NeZero m]

/-- The element form holds for a cover group `ZMod (2 * n) × ZMod m` with deck
translation `(n, t)`, where `t + t = 0`: the reduction
`ZMod (4 * n) × ZMod m → ZMod (2 * n) × ZMod m` of the first coordinate is
surjective with kernel `{0, (2 * n, 0)}`, and `(n, t)` has order four upstairs
and maps to the deck translation. -/
theorem elementForm_of_zmod_double
    (D : XDoubleCoverData (ZMod (2 * n) × ZMod m) H)
    (t : ZMod m) (ht : t + t = 0)
    (hdeck : D.deckS = (((n : ℕ) : ZMod (2 * n)), t)) :
    D.BocksteinElementForm :=
  D.elementForm_of_orderFourLift (zmodDoubleProj n m) (((n : ℕ) : ZMod (4 * n)), t)
    (addOrderOf_natCast_prod ht) zmodDoubleProj_surjective
    ((zmodDoubleProj_natCast t).trans hdeck.symm) (zmodDoubleProj_eq_zero_iff ht)

/-- `BocksteinVanishes` holds for a cover group `ZMod (2 * n) × ZMod m` with
deck translation `(n, t)`, where `t + t = 0`. -/
theorem bocksteinVanishes_of_zmod_double
    (D : XDoubleCoverData (ZMod (2 * n) × ZMod m) H)
    (t : ZMod m) (ht : t + t = 0)
    (hdeck : D.deckS = (((n : ℕ) : ZMod (2 * n)), t)) :
    D.BocksteinVanishes :=
  D.bocksteinVanishes_of_elementForm (D.elementForm_of_zmod_double t ht hdeck)

/-- For a cover group `ZMod (2 * n) × ZMod m` with deck translation `(n, t)`,
where `t + t = 0`, `dim (range ε_*) = k̃ - k`. -/
theorem finrank_range_epsH1_eq_of_zmod_double
    (D : XDoubleCoverData (ZMod (2 * n) × ZMod m) H)
    (t : ZMod m) (ht : t + t = 0)
    (hdeck : D.deckS = (((n : ℕ) : ZMod (2 * n)), t)) :
    dim₂ (LinearMap.range D.epsH1)
      = dim₂ D.coverComplex.H1 - dim₂ D.baseComplex.H1 :=
  D.finrank_range_epsH1_eq (D.bocksteinVanishes_of_zmod_double t ht hdeck)

/-- The element form holds for a cover group `ZMod m × ZMod (2 * n)` with deck
translation `(t, n)`, where `t + t = 0`: `elementForm_of_zmod_double` with the
two factors exchanged. -/
theorem elementForm_of_zmod_double_right
    (D : XDoubleCoverData (ZMod m × ZMod (2 * n)) H)
    (t : ZMod m) (ht : t + t = 0)
    (hdeck : D.deckS = (t, ((n : ℕ) : ZMod (2 * n)))) :
    D.BocksteinElementForm :=
  let e : ZMod (2 * n) × ZMod m ≃+ ZMod m × ZMod (2 * n) := AddEquiv.prodComm
  D.elementForm_of_orderFourLift (e.toAddMonoidHom.comp (zmodDoubleProj n m))
    (((n : ℕ) : ZMod (4 * n)), t) (addOrderOf_natCast_prod ht)
    (e.surjective.comp zmodDoubleProj_surjective)
    ((congrArg e (zmodDoubleProj_natCast t)).trans hdeck.symm)
    fun x => (map_eq_zero_iff e e.injective).trans (zmodDoubleProj_eq_zero_iff ht x)

/-- `BocksteinVanishes` holds for a cover group `ZMod m × ZMod (2 * n)` with
deck translation `(t, n)`, where `t + t = 0`. -/
theorem bocksteinVanishes_of_zmod_double_right
    (D : XDoubleCoverData (ZMod m × ZMod (2 * n)) H)
    (t : ZMod m) (ht : t + t = 0)
    (hdeck : D.deckS = (t, ((n : ℕ) : ZMod (2 * n)))) :
    D.BocksteinVanishes :=
  D.bocksteinVanishes_of_elementForm (D.elementForm_of_zmod_double_right t ht hdeck)

/-- For a cover group `ZMod m × ZMod (2 * n)` with deck translation `(t, n)`,
where `t + t = 0`, `dim (range ε_*) = k̃ - k`. -/
theorem finrank_range_epsH1_eq_of_zmod_double_right
    (D : XDoubleCoverData (ZMod m × ZMod (2 * n)) H)
    (t : ZMod m) (ht : t + t = 0)
    (hdeck : D.deckS = (t, ((n : ℕ) : ZMod (2 * n)))) :
    dim₂ (LinearMap.range D.epsH1)
      = dim₂ D.coverComplex.H1 - dim₂ D.baseComplex.H1 :=
  D.finrank_range_epsH1_eq (D.bocksteinVanishes_of_zmod_double_right t ht hdeck)

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum

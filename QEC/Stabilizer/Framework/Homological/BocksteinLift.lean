import QEC.Stabilizer.Framework.Homological.BBEpsFree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic

/-!
# The Bockstein composite vanishes on representatives

Let `R` be a commutative ring with `2 = 0` and `ε : R` an element whose
annihilator is `(ε ^ 3)`, and put `Q = R ⧸ (ε ^ 2)`. The main theorem
`bockstein_element_form` states that for `A B : R` and `z a b : Q` with
`A * z = ε * a` and `B * z = ε * b`, the element `A * b + B * a` lies in the
ideal `(ε * A, ε * B)` of `Q`.

In the intended instance `Q` is the group algebra of a double cover of a
bivariate bicycle code with polynomials `A`, `B`, the deck transformation is
`σ`, and `ε = 1 + σ`; `R` is the group algebra of a further cover in which `σ`
lifts to an element of order four. There `z` lifts a 2-cycle of the base code,
and `A * b + B * a` represents the image of its class under the composite
`H₂ → H₁ → H₀` of the two connecting maps of the base, a class that is defined
modulo `ε · (A, B)`. The theorem is the vanishing of that composite.

The proof has three steps, each a lemma:

- `rep_eq_zero_upstairs`: in `R`, the representative is a multiple of `ε ^ 3`,
  so it maps to `0` in `Q`;
- `exists_vanishing_choice_in_quotient`: hence in `Q` some choice of the
  quotients `a`, `b` makes the representative vanish;
- `mem_span_of_vanishing_choice`: two choices of `a`, `b` change the
  representative by an element of `(ε * A, ε * B)`, because the annihilator of
  `ε` in `Q` is `(ε)` (`ann_eps_quotient`).

`bockstein_element_form_of_surjective` is the same statement with the quotient
`R ⧸ (ε ^ 2)` replaced by any ring onto which `R` maps with kernel inside
`(ε ^ 2)` and with the square of the image of `ε` equal to zero; there the
ideal membership is spelled out as an equation.

`bockstein_element_form_deck` is the instance `R = 𝔽₂[X] ⧸ (X ^ 4)`, `ε = X`,
which is the group algebra of `ℤ/4` with `X = 1 + σ`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BocksteinLift

variable {R : Type*} [CommRing R]

/-- In a commutative ring with `2 = 0` in which the annihilator of `ε` is
`(ε ^ 3)`, if `A * z = ε * a` and `B * z = ε * b` then `A * b + B * a` is a
multiple of `ε ^ 3`: it is killed by `ε`, since
`ε * (A * b + B * a) = 2 * (A * B * z)`. -/
theorem rep_eq_zero_upstairs (ε A B z a b : R)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (hAz : A * z = ε * a) (hBz : B * z = ε * b) :
    ∃ v, A * b + B * a = ε ^ 2 * (ε * v) := by
  obtain ⟨v, hv⟩ := hann (A * b + B * a) (by
    linear_combination A * B * z * hchar - A * hBz - B * hAz)
  exact ⟨v, by linear_combination hv⟩

/-- If the annihilator of `ε` in `R` is `(ε ^ 3)`, then the annihilator of `ε`
in `R ⧸ (ε ^ 2)` is `(ε)`. -/
theorem ann_eps_quotient (ε : R)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (w : R ⧸ Ideal.span {ε ^ 2})
    (hw : Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * w = 0) :
    ∃ v, w = Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * v := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hw
  obtain ⟨r, hr⟩ := hw
  obtain ⟨v, hv⟩ := hann (w - ε * r) (by linear_combination hr)
  exact ⟨Ideal.Quotient.mk _ (r + ε ^ 2 * v), by
    rw [← map_mul, show w = ε * (r + ε ^ 2 * v) by linear_combination hv]⟩

/-- In `R ⧸ (ε ^ 2)`, if `A * z` and `B * z` are multiples of `ε`, then the
quotients `a₀`, `b₀` can be chosen with `A * b₀ + B * a₀ = 0`: lift `z` to `R`
and apply `rep_eq_zero_upstairs`. -/
theorem exists_vanishing_choice_in_quotient (ε A B : R)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (z a b : R ⧸ Ideal.span {ε ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ ε * a)
    (hBz : Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ ε * b) :
    ∃ a₀ b₀ : R ⧸ Ideal.span {ε ^ 2},
      Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ ε * a₀ ∧
      Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ ε * b₀ ∧
      Ideal.Quotient.mk _ A * b₀ + Ideal.Quotient.mk _ B * a₀ = 0 := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- the two congruences modulo `ε ^ 2` become equalities in `R`
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hAz hBz
  obtain ⟨rA, hrA⟩ := hAz
  obtain ⟨rB, hrB⟩ := hBz
  have hAz' : A * z = ε * (a + ε * rA) := by linear_combination hrA
  have hBz' : B * z = ε * (b + ε * rB) := by linear_combination hrB
  obtain ⟨v, hv⟩ := rep_eq_zero_upstairs ε A B z _ _ hchar hann hAz' hBz'
  refine ⟨Ideal.Quotient.mk _ (a + ε * rA), Ideal.Quotient.mk _ (b + ε * rB),
    by rw [← map_mul, ← map_mul, hAz'], by rw [← map_mul, ← map_mul, hBz'], ?_⟩
  rw [← map_mul, ← map_mul, ← map_add, hv]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨ε * v, rfl⟩)

/-- In a commutative ring in which the annihilator of `ε` is `(ε)`, if one
choice `a₀`, `b₀` of quotients of `A * z`, `B * z` by `ε` satisfies
`A * b₀ + B * a₀ = 0`, then every choice `a`, `b` has
`A * b + B * a ∈ (ε * A, ε * B)`. -/
theorem mem_span_of_vanishing_choice (ε A B z a b a₀ b₀ : R)
    (hannε : ∀ w : R, ε * w = 0 → ∃ v, w = ε * v)
    (hAz : ε * a = A * z) (hBz : ε * b = B * z)
    (hAz₀ : ε * a₀ = A * z) (hBz₀ : ε * b₀ = B * z)
    (h₀ : A * b₀ + B * a₀ = 0) :
    A * b + B * a ∈ Ideal.span {ε * A, ε * B} := by
  obtain ⟨va, hva⟩ := hannε (a - a₀) (by rw [mul_sub, hAz, hAz₀, sub_self])
  obtain ⟨vb, hvb⟩ := hannε (b - b₀) (by rw [mul_sub, hBz, hBz₀, sub_self])
  exact Ideal.mem_span_pair.mpr ⟨vb, va, by linear_combination -A * hvb - B * hva - h₀⟩

/-- Let `R` have `2 = 0` and the annihilator of `ε` equal to `(ε ^ 3)`. In
`R ⧸ (ε ^ 2)`, whenever `A * z = ε * a` and `B * z = ε * b`, the element
`A * b + B * a` lies in `(ε * A, ε * B)`. For the group algebra of a double
cover of a bivariate bicycle code this is the vanishing of the composite of the
two connecting maps `H₂ → H₁ → H₀` of the base. -/
theorem bockstein_element_form (ε A B : R)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (z a b : R ⧸ Ideal.span {ε ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ ε * a)
    (hBz : Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ ε * b) :
    Ideal.Quotient.mk _ A * b + Ideal.Quotient.mk _ B * a ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * Ideal.Quotient.mk _ A,
        Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * Ideal.Quotient.mk _ B} := by
  obtain ⟨a₀, b₀, hAz₀, hBz₀, h₀⟩ :=
    exists_vanishing_choice_in_quotient ε A B hchar hann z a b hAz hBz
  exact mem_span_of_vanishing_choice _ _ _ z a b a₀ b₀
    (ann_eps_quotient ε hann) hAz.symm hBz.symm hAz₀.symm hBz₀.symm h₀

/-- `bockstein_element_form` for a ring `S` in place of `R ⧸ (ε ^ 2)`. Let
`ρ : R →+* S` be surjective with kernel contained in `(ε ^ 2)`, and let
`ε' = ρ ε` satisfy `ε' ^ 2 = 0`, where `R` has `2 = 0` and the annihilator of
`ε` equal to `(ε ^ 3)`. If `A * z = ε' * a` and `B * z = ε' * b` in `S`, then
`A * b + B * a = ε' * (A * r + B * s)` for some `r s : S`: lift everything to
`R` and apply `rep_eq_zero_upstairs`. -/
theorem bockstein_element_form_of_surjective {S : Type*} [CommRing S] (ρ : R →+* S)
    (hρ : Function.Surjective ρ) {ε : R} {ε' : S} (hε : ρ ε = ε') (hε' : ε' ^ 2 = 0)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (hker : ∀ x : R, ρ x = 0 → ε ^ 2 ∣ x)
    {A B z a b : S} (hAz : A * z = ε' * a) (hBz : B * z = ε' * b) :
    ∃ r s : S, A * b + B * a = ε' * (A * r + B * s) := by
  subst hε
  obtain ⟨A, rfl⟩ := hρ A
  obtain ⟨B, rfl⟩ := hρ B
  obtain ⟨z, rfl⟩ := hρ z
  obtain ⟨a, rfl⟩ := hρ a
  obtain ⟨b, rfl⟩ := hρ b
  obtain ⟨rA, hrA⟩ := hker (A * z - ε * a) (by rw [map_sub, map_mul, map_mul, hAz, sub_self])
  obtain ⟨rB, hrB⟩ := hker (B * z - ε * b) (by rw [map_sub, map_mul, map_mul, hBz, sub_self])
  obtain ⟨v, hv⟩ := rep_eq_zero_upstairs ε A B z (a + ε * rA) (b + ε * rB) hchar hann
    (by linear_combination hrA) (by linear_combination hrB)
  have h := congrArg ρ hv
  simp only [map_add, map_mul, map_pow] at h
  exact ⟨-ρ rB, -ρ rA, by linear_combination h + ρ ε * ρ v * hε'⟩

/-! ## The group algebra of `ℤ/4`

In characteristic two `X ^ 4 - 1 = (X - 1) ^ 4`, so the group algebra `𝔽₂[ℤ/4]`
is the truncated polynomial ring `𝔽₂[X] ⧸ (X ^ 4)`, with `X` the class of
`1 + σ` for a generator `σ`. It satisfies both hypotheses of
`bockstein_element_form`, which therefore holds unconditionally on its quotient
by `(X ^ 2)`, the group algebra of `ℤ/2`. -/

open Polynomial in
/-- The truncated polynomial ring `𝔽₂[X] ⧸ (X ^ 4)`, isomorphic to the group
algebra `𝔽₂[ℤ/4]`. -/
abbrev DeckRing := Polynomial (ZMod 2) ⧸ Ideal.span {(X : Polynomial (ZMod 2)) ^ 4}

open Polynomial in
/-- The class of `X` in `DeckRing`; it corresponds to `1 + σ` for a generator
`σ` of `ℤ/4`. -/
noncomputable abbrev deckEps : DeckRing := Ideal.Quotient.mk _ (X : Polynomial (ZMod 2))

/-- `DeckRing` has `2 = 0`. -/
theorem deckRing_two : (2 : DeckRing) = 0 :=
  BBEpsFree.two_eq_zero_of_algebra (k := ZMod 2) DeckRing (by decide)

/-- The annihilator of `deckEps` in `DeckRing` is `(deckEps ^ 3)`. -/
theorem deckRing_ann : ∀ w : DeckRing, deckEps * w = 0 → ∃ v, w = deckEps ^ 3 * v :=
  BBEpsFree.hann_of_epsFree (BBEpsFree.epsFree_quotXpow 4)

/-- `bockstein_element_form` for `R = DeckRing` and `ε = deckEps`, where both
ring hypotheses hold. -/
theorem bockstein_element_form_deck (A B : DeckRing)
    (z a b : DeckRing ⧸ Ideal.span {deckEps ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ deckEps * a)
    (hBz : Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ deckEps * b) :
    Ideal.Quotient.mk _ A * b + Ideal.Quotient.mk _ B * a ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {deckEps ^ 2}) deckEps * Ideal.Quotient.mk _ A,
        Ideal.Quotient.mk (Ideal.span {deckEps ^ 2}) deckEps * Ideal.Quotient.mk _ B} :=
  bockstein_element_form deckEps A B deckRing_two deckRing_ann z a b hAz hBz

end BocksteinLift
end Homological
end Stabilizer
end Quantum

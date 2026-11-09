import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank of the composite in an exact transfer sequence

Linear algebra behind the rank of the deck image on the homology of a double
cover. Let `p : Hc → Hb` and `τ : Hb → Hc` be linear maps of finite-dimensional
spaces with `ker p = range τ`, and put `ε = τ ∘ p`. In the intended instance
`Hc` and `Hb` are the first homologies of the cover and of the base, `p` is the
pushforward, `τ` the transfer, and `ε` is the action of `1 + σ` for the deck
transformation `σ`.

- `finrank_range_comp_add_eq`: the exact identity
  `dim (range ε) + dim Hb + dim (range p ⊓ ker τ) = dim Hc + dim (ker τ)`;
- `finrank_sub_le_finrank_range_comp`: the bound
  `dim Hc - dim Hb ≤ dim (range ε)`;
- `finrank_range_comp_eq_of_ker_le`: equality when `ker τ ≤ range p`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBBocksteinRank

open Module LinearMap

variable {F Hc Hb : Type*} [Field F]
  [AddCommGroup Hc] [Module F Hc] [FiniteDimensional F Hc]
  [AddCommGroup Hb] [Module F Hb] [FiniteDimensional F Hb]

omit [FiniteDimensional F Hc] in
/-- Rank–nullity for the restriction of `τ` to a subspace `U`:
`dim τ(U) + dim (U ⊓ ker τ) = dim U`. -/
lemma finrank_map_add_finrank_inf_ker (τ : Hb →ₗ[F] Hc) (U : Submodule F Hb) :
    finrank F (U.map τ) + finrank F (U ⊓ ker τ : Submodule F Hb) = finrank F U := by
  rw [← finrank_range_add_finrank_ker (τ.domRestrict U), range_domRestrict, ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype]

/-- With `ker p = range τ`, the composite `ε = τ ∘ p` satisfies
`dim (range ε) + dim Hb + dim (range p ⊓ ker τ) = dim Hc + dim (ker τ)`.

The term `range p ⊓ ker τ` is the whole defect of
`finrank_sub_le_finrank_range_comp`: it is at most `dim (ker τ)`, with equality
exactly when `ker τ ≤ range p`. -/
theorem finrank_range_comp_add_eq (p : Hc →ₗ[F] Hb) (τ : Hb →ₗ[F] Hc)
    (hexact : ker p = range τ) :
    finrank F (range (τ ∘ₗ p)) + finrank F Hb
        + finrank F (range p ⊓ ker τ : Submodule F Hb)
      = finrank F Hc + finrank F (ker τ) := by
  have hε := finrank_map_add_finrank_inf_ker τ (range p)
  rw [← range_comp] at hε
  have hp := finrank_range_add_finrank_ker p
  rw [hexact] at hp
  have hτ := finrank_range_add_finrank_ker τ
  omega

/-- With `ker p = range τ`, the image of the composite `ε = τ ∘ p` has dimension
at least `dim Hc - dim Hb`. -/
theorem finrank_sub_le_finrank_range_comp (p : Hc →ₗ[F] Hb) (τ : Hb →ₗ[F] Hc)
    (hexact : ker p = range τ) :
    finrank F Hc - finrank F Hb ≤ finrank F (range (τ ∘ₗ p)) := by
  have hid := finrank_range_comp_add_eq p τ hexact
  have hle := Submodule.finrank_mono (inf_le_right : range p ⊓ ker τ ≤ ker τ)
  omega

/-- With `ker p = range τ` and `ker τ ≤ range p`, the image of the composite
`ε = τ ∘ p` has dimension exactly `dim Hc - dim Hb`. -/
theorem finrank_range_comp_eq_of_ker_le (p : Hc →ₗ[F] Hb) (τ : Hb →ₗ[F] Hc)
    (hexact : ker p = range τ) (hle : ker τ ≤ range p) :
    finrank F (range (τ ∘ₗ p)) = finrank F Hc - finrank F Hb := by
  have hid := finrank_range_comp_add_eq p τ hexact
  rw [inf_of_le_right hle] at hid
  omega

end BBBocksteinRank
end Homological
end Stabilizer
end Quantum

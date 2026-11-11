import QEC.Stabilizer.Framework.Homological.BBDuality
import QEC.Stabilizer.Framework.Homological.ToCode

/-!
# The number of logical qubits of a bivariate bicycle code

For the bivariate bicycle chain complex `bbChainComplex A B` over a finite
abelian group `G`, the first homology has dimension

```
dim H₁ = 2 · dim (ker A ⊓ ker B)
```

(`finrank_H1_bbChainComplex`), where `A` and `B` act on `G → ZMod 2` by
convolution (`convLin`) and `ker a` is the scoped notation for the kernel of
convolution by `a`. This is the number of logical qubits of the code, the `k`
of `bbStabilizerCode`.

## The argument

`dim H₁ = dim Z₁ − dim B₁`, with rank-nullity for `∂₁`, `∂₂` and the cut map,
and `rank cutMap = rank ∂₁` since the two are transposes
(`HomologicalCode.finrank_range_cutMap`). It remains to name two kernels:

* `ker_bbBoundary2`: `ker ∂₂ = ker A ⊓ ker B`, as `∂₂ f = (A ⋆ f | B ⋆ f)`;
* `ker_cutMap`: `ker cutMap = ker (reflect A) ⊓ ker (reflect B)`, as the cut
  map is `s ↦ (reflect B ⋆ s | reflect A ⋆ s)` (`bb_cutMap_eq`), where
  `reflect a = a ∘ (-·)`.

The two kernels have the same dimension (`finrank_ker_inf_ker_reflect`):
reflection is a linear automorphism of the chain space (`reflectLin`) carrying
one onto the other, since `reflect (a ⋆ f) = reflect a ⋆ reflect f`.

Writing `κ = dim (ker A ⊓ ker B)`, this gives `rank ∂₂ = rank ∂₁ = |G| − κ`, so
`dim Z₁ = 2|G| − (|G| − κ)`, `dim B₁ = |G| − κ` and `dim H₁ = 2κ`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Reflection as a linear automorphism of the chain space -/

section ReflectLin

variable {G : Type} [AddCommGroup G]

/-- Reflection through the group inverse, `f ↦ (g ↦ f (-g))`, as a linear
automorphism of the chain space. It is its own inverse. -/
noncomputable def reflectLin : (G → ZMod 2) ≃ₗ[ZMod 2] (G → ZMod 2) where
  toFun := reflect
  invFun := reflect
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := reflect_reflect
  right_inv := reflect_reflect

@[simp] lemma reflectLin_apply (f : G → ZMod 2) : reflectLin f = reflect f := rfl

@[simp] lemma reflectLin_symm_apply (f : G → ZMod 2) : reflectLin.symm f = reflect f := rfl

end ReflectLin

/-! ## Convolution as a linear map, and its kernel -/

section Kernel

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Convolution by `a`, `f ↦ a ⋆ f`, as a `ZMod 2`-linear endomorphism of the
chain space `G → ZMod 2`: the action of `a ∈ 𝔽₂[G]` on the group algebra. -/
noncomputable def convLin (a : G → ZMod 2) : (G → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) where
  toFun f := a ⋆ f
  map_add' f₁ f₂ := conv_add_right a f₁ f₂
  map_smul' s f := conv_smul_right s a f

@[simp] lemma convLin_apply (a f : G → ZMod 2) : convLin a f = a ⋆ f := rfl

/-- `ker a` is the kernel of convolution by `a`, `LinearMap.ker (convLin a)`:
the chains `f` with `a ⋆ f = 0`. Scoped to `Quantum.Stabilizer.Homological.BB`
like `⋆`; `ker A ⊓ ker B` is the common kernel whose dimension is half the
number of logical qubits (`finrank_H1_bbChainComplex`). -/
scoped notation:max "ker " a:max => LinearMap.ker (convLin a)

/-- `f` lies in `ker A ⊓ ker B` iff `A ⋆ f = 0` and `B ⋆ f = 0`. -/
lemma mem_ker_inf_ker {A B f : G → ZMod 2} :
    f ∈ ker A ⊓ ker B ↔ A ⋆ f = 0 ∧ B ⋆ f = 0 :=
  Iff.rfl

/-- `ker ∂₂ = ker A ⊓ ker B`: `∂₂ f = (A ⋆ f | B ⋆ f)` vanishes iff both
halves do. -/
theorem ker_bbBoundary2 (A B : G → ZMod 2) :
    LinearMap.ker (bbBoundary2 A B) = ker A ⊓ ker B :=
  Submodule.ext fun f => bbBoundary2Fn_eq_zero_iff A B f

/-- `reflect a ⋆ f = 0 ↔ a ⋆ reflect f = 0`: reflection is multiplicative and
injective. -/
lemma reflect_conv_eq_zero_iff (a f : G → ZMod 2) :
    reflect a ⋆ f = 0 ↔ a ⋆ reflect f = 0 := by
  conv_lhs => rw [← reflect_reflect f, ← reflect_conv]
  exact reflect_eq_zero_iff _

/-- `f` lies in `ker (reflect A) ⊓ ker (reflect B)` iff `reflect f` lies in
`ker A ⊓ ker B`. -/
lemma mem_ker_inf_ker_reflect_iff (A B f : G → ZMod 2) :
    f ∈ ker (reflect A) ⊓ ker (reflect B) ↔ reflect f ∈ ker A ⊓ ker B := by
  rw [mem_ker_inf_ker, mem_ker_inf_ker, reflect_conv_eq_zero_iff, reflect_conv_eq_zero_iff]

/-- Reflection maps `ker A ⊓ ker B` onto `ker (reflect A) ⊓ ker (reflect B)`. -/
theorem ker_inf_ker_map_reflectLin (A B : G → ZMod 2) :
    (ker A ⊓ ker B).map (reflectLin (G := G)).toLinearMap =
      ker (reflect A) ⊓ ker (reflect B) := by
  ext f
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_inf_ker_reflect_iff]
  exact Iff.rfl

/-- `dim (ker (reflect A) ⊓ ker (reflect B)) = dim (ker A ⊓ ker B)`. -/
theorem finrank_ker_inf_ker_reflect (A B : G → ZMod 2) :
    Module.finrank (ZMod 2) ↥(ker (reflect A) ⊓ ker (reflect B)) =
      Module.finrank (ZMod 2) ↥(ker A ⊓ ker B) := by
  rw [← ker_inf_ker_map_reflectLin, LinearEquiv.finrank_map_eq]

end Kernel

/-! ## The kernel of the cut map, and the logical-qubit count -/

section LogicalQubits

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- `ker cutMap = ker (reflect A) ⊓ ker (reflect B)`: by `bb_cutMap_eq` the cut
map is `s ↦ (reflect B ⋆ s | reflect A ⋆ s)`, which vanishes iff both halves
do. -/
theorem ker_cutMap (A B : G → ZMod 2) :
    LinearMap.ker (bbChainComplex A B).cutMap = ker (reflect A) ⊓ ker (reflect B) := by
  ext s
  change (bbChainComplex A B).cutMap s = 0 ↔ reflect A ⋆ s = 0 ∧ reflect B ⋆ s = 0
  rw [bb_cutMap_eq, and_comm]
  exact halves_ext_iff

/-- The first homology of the bivariate bicycle chain complex has dimension
`dim H₁ = 2 · dim (ker A ⊓ ker B)`. -/
theorem finrank_H1_bbChainComplex (A B : G → ZMod 2) :
    Module.finrank (ZMod 2) (bbChainComplex A B).H1 =
      2 * Module.finrank (ZMod 2) ↥(ker A ⊓ ker B) := by
  have hrn1 := (bbChainComplex A B).rank_nullity_boundary1
  have hrn2 := (bbChainComplex A B).rank_nullity_boundary2
  have hcut := (bbChainComplex A B).finrank_range_cutMap
  have hcutrn := LinearMap.finrank_range_add_finrank_ker (bbChainComplex A B).cutMap
  have hC0 := (bbChainComplex A B).finrank_C0
  have hC1 := (bbChainComplex A B).finrank_C1
  have hC2 := (bbChainComplex A B).finrank_C2
  have hcard0 : Fintype.card (bbChainComplex A B).C0 = Fintype.card G := rfl
  have hcard1 : Fintype.card (bbChainComplex A B).C1 = 2 * Fintype.card G := bbCard_C1
  have hcard2 : Fintype.card (bbChainComplex A B).C2 = Fintype.card G := rfl
  have hker2 : Module.finrank (ZMod 2) (LinearMap.ker (bbChainComplex A B).boundary2) =
      Module.finrank (ZMod 2) ↥(ker A ⊓ ker B) := by
    change Module.finrank (ZMod 2) (LinearMap.ker (bbBoundary2 A B)) = _
    rw [ker_bbBoundary2]
  have hkerc : Module.finrank (ZMod 2) (LinearMap.ker (bbChainComplex A B).cutMap) =
      Module.finrank (ZMod 2) ↥(ker A ⊓ ker B) := by
    rw [ker_cutMap]
    exact finrank_ker_inf_ker_reflect A B
  rw [(bbChainComplex A B).finrank_H1_eq_cycles_sub_boundaries]
  omega

end LogicalQubits

end BB
end Homological
end Stabilizer
end Quantum

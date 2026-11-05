import QEC.Stabilizer.Framework.Homological.BBDuality
import QEC.Stabilizer.Framework.Homological.ToCode

/-!
# The number of logical qubits of a bivariate bicycle code

For the bivariate bicycle chain complex `bbChainComplex A B` over a finite
abelian group `G`, the first homology has dimension

```
dim H₁ = 2 · dim (ker A ∩ ker B)
```

where `A` and `B` act on `G → ZMod 2` by convolution (`convLin`), and
`ker A ∩ ker B` is `commonKernel A B`. This is the logical-qubit count of
Bravyi–Cross–Gambetta–Maslov–Rall–Yoder, *High-threshold and low-overhead
fault-tolerant quantum memory* (Nature 627, 2024), Lemma 1, and it is what
`bbStabilizerCode` (`BBStabilizerCode.lean`) uses as its `k`.

## The argument

`ToCode.lean` and `Code.lean` give `dim H₁ = dim Z₁ − dim B₁` together with
rank-nullity for `∂₁`, `∂₂`, and the cut map, and `rank cutMap = rank ∂₁`
(`finrank_range_cutMap`, since the two are transposes). It remains to name
the two kernels:

- `ker ∂₂ = ker A ∩ ker B` (`ker_bbBoundary2`): `∂₂ f = (A ⋆ f | B ⋆ f)`.
- `ker cutMap = ker (reflect A) ∩ ker (reflect B)` (`ker_cutMap`): by the
  transpose formula `bb_cutMap_eq` of `BBDuality.lean`, the cut map is
  `s ↦ (reflect B ⋆ s | reflect A ⋆ s)`, where `reflect a = a ∘ (-·)` is the
  group-algebra antipode.
- The two kernels have the same dimension
  (`finrank_commonKernel_reflect`): reflection is a linear automorphism of
  the chain space carrying one onto the other, since
  `reflect (a ⋆ f) = reflect a ⋆ reflect f`.

Writing `κ = dim (ker A ∩ ker B)` and `|G|` for the group order,
`rank ∂₂ = rank ∂₁ = |G| − κ`, so `dim Z₁ = 2|G| − (|G| − κ)`,
`dim B₁ = |G| − κ`, and `dim H₁ = 2κ`.
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

/-! ## Convolution as a linear map, and the common kernel -/

section CommonKernel

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Convolution by `a`, `f ↦ a ⋆ f`, as a `ZMod 2`-linear endomorphism of the
chain space `G → ZMod 2`: the action of `a ∈ 𝔽₂[G]` on the group algebra. -/
noncomputable def convLin (a : G → ZMod 2) : (G → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) where
  toFun f := a ⋆ f
  map_add' f₁ f₂ := conv_add_right a f₁ f₂
  map_smul' s f := conv_smul_right s a f

@[simp] lemma convLin_apply (a f : G → ZMod 2) : convLin a f = a ⋆ f := rfl

/-- `ker A ∩ ker B`: the chains annihilated by convolution with both `A` and
`B`. Half the number of logical qubits of the bivariate bicycle code
(`finrank_H1_bbChainComplex`). -/
noncomputable def commonKernel (A B : G → ZMod 2) : Submodule (ZMod 2) (G → ZMod 2) :=
  LinearMap.ker (convLin A) ⊓ LinearMap.ker (convLin B)

lemma mem_commonKernel {A B f : G → ZMod 2} :
    f ∈ commonKernel A B ↔ A ⋆ f = 0 ∧ B ⋆ f = 0 :=
  Iff.rfl

/-- `ker ∂₂ = ker A ∩ ker B`: `∂₂ f = (A ⋆ f | B ⋆ f)` vanishes iff both
halves do. -/
theorem ker_bbBoundary2 (A B : G → ZMod 2) :
    LinearMap.ker (bbBoundary2 A B) = commonKernel A B := by
  ext f
  rw [LinearMap.mem_ker, mem_commonKernel]
  constructor
  · intro h
    refine ⟨funext fun g => ?_, funext fun g => ?_⟩
    · have h0 : bbBoundary2Fn A B f (g, 0) = 0 := congrFun h (g, 0)
      simpa [bbBoundary2Fn] using h0
    · have h1 : bbBoundary2Fn A B f (g, 1) = 0 := congrFun h (g, 1)
      simpa [bbBoundary2Fn] using h1
  · rintro ⟨hA, hB⟩
    funext ⟨g, j⟩
    change bbBoundary2Fn A B f (g, j) = 0
    simp only [bbBoundary2Fn]
    split_ifs
    · exact congrFun hA g
    · exact congrFun hB g

/-- `reflect a ⋆ f = 0 ↔ a ⋆ reflect f = 0`: reflection is multiplicative and
injective. -/
lemma reflect_conv_eq_zero_iff (a f : G → ZMod 2) :
    reflect a ⋆ f = 0 ↔ a ⋆ reflect f = 0 := by
  conv_lhs => rw [← reflect_reflect f, ← reflect_conv]
  exact reflect_eq_zero_iff _

lemma mem_commonKernel_reflect_iff (A B f : G → ZMod 2) :
    f ∈ commonKernel (reflect A) (reflect B) ↔ reflect f ∈ commonKernel A B := by
  rw [mem_commonKernel, mem_commonKernel, reflect_conv_eq_zero_iff, reflect_conv_eq_zero_iff]

/-- Reflection maps `ker A ∩ ker B` onto `ker (reflect A) ∩ ker (reflect B)`. -/
theorem commonKernel_map_reflectLin (A B : G → ZMod 2) :
    (commonKernel A B).map (reflectLin (G := G)).toLinearMap =
      commonKernel (reflect A) (reflect B) := by
  ext f
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_commonKernel_reflect_iff]
  exact Iff.rfl

/-- `dim (ker (reflect A) ∩ ker (reflect B)) = dim (ker A ∩ ker B)`. -/
theorem finrank_commonKernel_reflect (A B : G → ZMod 2) :
    Module.finrank (ZMod 2) (commonKernel (reflect A) (reflect B)) =
      Module.finrank (ZMod 2) (commonKernel A B) := by
  rw [← commonKernel_map_reflectLin, LinearEquiv.finrank_map_eq]

end CommonKernel

/-! ## The kernel of the cut map, and the logical-qubit count -/

section LogicalQubits

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- `ker cutMap = ker (reflect A) ∩ ker (reflect B)`: by the transpose formula
`bb_cutMap_eq`, `cutMap s = (reflect B ⋆ s | reflect A ⋆ s)`. -/
theorem ker_cutMap (A B : G → ZMod 2) :
    LinearMap.ker (bbChainComplex A B).cutMap = commonKernel (reflect A) (reflect B) := by
  ext s
  rw [LinearMap.mem_ker, bb_cutMap_eq]
  change _ ↔ reflect A ⋆ s = 0 ∧ reflect B ⋆ s = 0
  constructor
  · intro h
    refine ⟨funext fun g => ?_, funext fun g => ?_⟩
    · simpa using congrFun h (g, 1)
    · simpa using congrFun h (g, 0)
  · rintro ⟨hA, hB⟩
    funext ⟨g, j⟩
    split_ifs
    · exact congrFun hB g
    · exact congrFun hA g

/-- **`dim H₁ = 2 · dim (ker A ∩ ker B)`** for the bivariate bicycle chain
complex (Bravyi et al. 2024, Lemma 1). -/
theorem finrank_H1_bbChainComplex (A B : G → ZMod 2) :
    Module.finrank (ZMod 2) (bbChainComplex A B).H1 =
      2 * Module.finrank (ZMod 2) (commonKernel A B) := by
  have hH1 := (bbChainComplex A B).finrank_H1_eq_cycles_sub_boundaries
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
      Module.finrank (ZMod 2) (commonKernel A B) := by
    change Module.finrank (ZMod 2) (LinearMap.ker (bbBoundary2 A B)) = _
    rw [ker_bbBoundary2]
  have hkerc : Module.finrank (ZMod 2) (LinearMap.ker (bbChainComplex A B).cutMap) =
      Module.finrank (ZMod 2) (commonKernel A B) := by
    rw [ker_cutMap]
    exact finrank_commonKernel_reflect A B
  rw [hH1]
  omega

end LogicalQubits

end BB
end Homological
end Stabilizer
end Quantum

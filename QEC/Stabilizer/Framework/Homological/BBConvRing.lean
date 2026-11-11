import QEC.Stabilizer.Framework.Homological.BBChainComplex
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Convolution is the product of the group algebra

The chains of a bivariate bicycle complex are functions `G → ZMod 2`,
multiplied by the convolution `conv`; the ring structure that `G → ZMod 2`
carries as a type is the pointwise one. The group algebra
`AddMonoidAlgebra (ZMod 2) G` is the same `ZMod 2`-module with convolution as
its ring multiplication. This file identifies the two, so that ring-theoretic
facts proved in the group algebra apply to chains:

* `convEquiv : AddMonoidAlgebra (ZMod 2) G ≃ₗ[ZMod 2] (G → ZMod 2)` sends an
  element of the group algebra to its coefficient function;
* `convEquiv_mul`: `convEquiv (a * b) = convEquiv a ⋆ convEquiv b`;
* `convEquiv_single`: the monomial `single s r` is the point mass
  `Pi.single s r`;
* `conv_convEquiv_single`: convolution by the monomial of `s` is translation by
  `-s`, and `conv_convEquiv_one_add_single`: the element `1 + single σ 1` acts
  on chains as `v ↦ v + translate (-σ) v`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

variable {G : Type} [Fintype G]

/-- The `ZMod 2`-linear equivalence between the group algebra `𝔽₂[G]` and the
chain space `G → ZMod 2`, sending an element to its coefficient function. -/
noncomputable def convEquiv :
    AddMonoidAlgebra (ZMod 2) G ≃ₗ[ZMod 2] (G → ZMod 2) :=
  Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) G

@[simp] lemma convEquiv_apply (a : AddMonoidAlgebra (ZMod 2) G) (g : G) :
    convEquiv a g = a g := rfl

@[simp] lemma convEquiv_symm_apply (a : G → ZMod 2) (g : G) :
    (convEquiv.symm a) g = a g := rfl

/-- The monomial `single s r` of the group algebra is the point mass
`Pi.single s r`. -/
lemma convEquiv_single [DecidableEq G] (s : G) (r : ZMod 2) :
    convEquiv (AddMonoidAlgebra.single s r) = Pi.single s r :=
  Finsupp.single_eq_pi_single s r

variable [AddCommGroup G]

/-- Convolution is the group-algebra product: `convEquiv` carries the
multiplication of `𝔽₂[G]` to `conv`. -/
lemma convEquiv_mul (a b : AddMonoidAlgebra (ZMod 2) G) :
    convEquiv (a * b) = convEquiv a ⋆ convEquiv b := by
  funext g
  rw [convEquiv_apply, conv_apply, AddMonoidAlgebra.mul_apply_left, Finsupp.sum_fintype]
  · simp [sub_eq_neg_add]
  · simp

/-- Convolution by the monomial of `s` is translation by `-s`:
`convEquiv (single s 1) ⋆ v = translate (-s) v`. -/
lemma conv_convEquiv_single (s : G) (v : G → ZMod 2) :
    convEquiv (AddMonoidAlgebra.single s 1) ⋆ v = translate (-s) v := by
  classical
  rw [convEquiv_single, conv_single_left]
  exact funext fun g => congrArg v (sub_eq_add_neg g s)

/-- The element `1 + single σ 1` of the group algebra acts on chains as
`v ↦ v + translate (-σ) v`. -/
lemma conv_convEquiv_one_add_single (σ : G) (v : G → ZMod 2) :
    convEquiv (1 + AddMonoidAlgebra.single σ 1) ⋆ v = v + translate (-σ) v := by
  classical
  rw [map_add, conv_add_left, conv_convEquiv_single, AddMonoidAlgebra.one_def,
    convEquiv_single, conv_single_left]
  simp

end BB
end Homological
end Stabilizer
end Quantum

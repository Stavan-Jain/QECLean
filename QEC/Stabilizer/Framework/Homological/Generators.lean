import QEC.Stabilizer.Framework.Homological.CSS
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Symplectic.SupportLemmas
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner

/-!
# Stabilizer generators of a homological CSS code

For a `HomologicalCode X`, the X-check at a 2-cell `f` is the face stabilizer
`faceStabOf f = chainXOperator (∂₂ δ_f)`, and the Z-check at a 0-cell `v` is
the vertex stabilizer `vertexStabOf v = chainZOperator (cutMap δ_v)`. Their
ranges are the generator sets `XGenerators` and `ZGenerators`.

Commutation with a chain operator is read off the pairing
`chainInnerProduct c c' = ∑ e, c e * c' e` of 1-chains:

* `commutes_chainZOperator_iff`: a Pauli group element `g` commutes with
  `chainZOperator c` iff its X-support chain `xChainOf g` pairs to `0` with
  `c`; `chainXOperator_commutes_iff` is the statement for `chainXOperator c`
  and the Z-support chain `zChainOf g`;
* `chainXOperator_commutes_chainZOperator_iff`: two chain operators of
  opposite types commute iff their chains pair to `0`;
* `faceStabOf_commutes_vertexStabOf`, `ZGenerators_commute_XGenerators`: the
  checks commute, since `⟨∂₂ f, cutMap s⟩ = ⟨∂₁ (∂₂ f), s⟩ = 0`
  (`chainInnerProduct_boundary2_cutMap_eq_zero`).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators
open scoped NQubitPauliGroupElement
open NQubitPauliGroupElement (IsXTypeElement IsZTypeElement)

namespace HomologicalCode

variable (X : HomologicalCode)

/-- Indicator chain of a single 2-cell. -/
noncomputable def singleFace (f : X.C2) : X.C2 → ZMod 2 := Pi.single f 1

/-- Indicator chain of a single 0-cell. -/
noncomputable def singleVtx (v : X.C0) : X.C0 → ZMod 2 := Pi.single v 1

/-- Indicator chain of a single 1-cell. -/
noncomputable def singleEdge (e : X.C1) : X.C1 → ZMod 2 := Pi.single e 1

/-- The X-check at the 2-cell `f`: the X-chain operator of `∂₂ δ_f`. -/
noncomputable def faceStabOf (f : X.C2) :
    NQubitPauliGroupElement X.numQubits :=
  X.chainXOperator (X.boundary2 (X.singleFace f))

/-- The Z-check at the 0-cell `v`: the Z-chain operator of `cutMap δ_v`. -/
noncomputable def vertexStabOf (v : X.C0) :
    NQubitPauliGroupElement X.numQubits :=
  X.chainZOperator (X.cutMap (X.singleVtx v))

/-- The set of X stabilizer generators. -/
noncomputable def XGenerators : Set (NQubitPauliGroupElement X.numQubits) :=
  Set.range X.faceStabOf

/-- The set of Z stabilizer generators. -/
noncomputable def ZGenerators : Set (NQubitPauliGroupElement X.numQubits) :=
  Set.range X.vertexStabOf

variable {X}

/-- `chainXOperator (∂₂ δ_f)` is the X-check at `f`. -/
@[simp] lemma chainXOperator_boundary2_singleFace (f : X.C2) :
    X.chainXOperator (X.boundary2 (X.singleFace f)) = X.faceStabOf f := rfl

/-- `chainZOperator (cutMap δ_v)` is the Z-check at `v`. -/
@[simp] lemma chainZOperator_cutMap_singleVtx (v : X.C0) :
    X.chainZOperator (X.cutMap (X.singleVtx v)) = X.vertexStabOf v := rfl

/-- Every X-check is X-type. -/
lemma faceStabOf_isXType (f : X.C2) : IsXTypeElement (X.faceStabOf f) :=
  chainXOperator_isXType _

/-- Every Z-check is Z-type. -/
lemma vertexStabOf_isZType (v : X.C0) : IsZTypeElement (X.vertexStabOf v) :=
  chainZOperator_isZType _

/-- Every X generator is X-type. -/
lemma XGenerators_isXType : ∀ g ∈ X.XGenerators, IsXTypeElement g := by
  rintro _ ⟨f, rfl⟩
  exact faceStabOf_isXType f

/-- Every Z generator is Z-type. -/
lemma ZGenerators_isZType : ∀ g ∈ X.ZGenerators, IsZTypeElement g := by
  rintro _ ⟨v, rfl⟩
  exact vertexStabOf_isZType v

/-! ## The pairing of 1-chains -/

/-- The standard bilinear pairing of 1-chains over `𝔽₂`. -/
noncomputable def chainInnerProduct (c c' : X.C1 → ZMod 2) : ZMod 2 :=
  ∑ e : X.C1, c e * c' e

/-- A boundary pairs to `0` with a cut: `⟨∂₂ f, cutMap s⟩ = ⟨∂₁ (∂₂ f), s⟩ = 0`
by `boundary1_cutMap_transpose` and the chain-complex law. -/
theorem chainInnerProduct_boundary2_cutMap_eq_zero
    (f : X.C2 → ZMod 2) (s : X.C0 → ZMod 2) :
    chainInnerProduct (X.boundary2 f) (X.cutMap s) = 0 := by
  rw [chainInnerProduct, ← X.boundary1_cutMap_transpose, X.boundary_comp_apply f]
  simp

/-- Pairing with the cut of a single vertex evaluates the boundary there:
`⟨c, cutMap δ_v⟩ = (∂₁ c) v`. -/
theorem chainInnerProduct_cutMap_singleVtx_eq_boundary1
    (c : X.C1 → ZMod 2) (v : X.C0) :
    chainInnerProduct c (X.cutMap (X.singleVtx v)) = X.boundary1 c v := by
  rw [chainInnerProduct, ← X.boundary1_cutMap_transpose c (X.singleVtx v)]
  simp [singleVtx, Pi.single_apply]

/-- Pairing with the boundary of a single face evaluates the dual boundary
there: `⟨∂₂ δ_f, c⟩ = (dualBoundary c) f`. -/
theorem chainInnerProduct_boundary2_singleFace_eq_dualBoundary
    (c : X.C1 → ZMod 2) (f : X.C2) :
    chainInnerProduct (X.boundary2 (X.singleFace f)) c = X.dualBoundary c f := by
  rw [chainInnerProduct, boundary2_dualBoundary_transpose]
  simp [singleFace, Pi.single_apply]

/-! ## Commutation with chain operators -/

/-- The symplectic inner product of a Pauli group element `g` with a Z-chain
operator is the pairing of the X-support chain of `g` with the chain. -/
lemma symplecticInner_chainZOperator_right (g : NQubitPauliGroupElement X.numQubits)
    (c : X.C1 → ZMod 2) :
    ⟪g, X.chainZOperator c⟫ₛ = chainInnerProduct (X.xChainOf g) c := by
  rw [NQubitPauliOperator.symplecticInner, ← X.edgeEquiv.sum_comp, chainInnerProduct]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [chainZOperator_operators_edgeEquiv, xChainOf]
  generalize g.operators (X.edgeEquiv e) = P
  obtain h | h := zmod2_eq_zero_or_eq_one (c e) <;> cases P <;> simp [h]

/-- The symplectic inner product of an X-chain operator with a Pauli group
element `g` is the pairing of the chain with the Z-support chain of `g`. -/
lemma symplecticInner_chainXOperator_left (c : X.C1 → ZMod 2)
    (g : NQubitPauliGroupElement X.numQubits) :
    ⟪X.chainXOperator c, g⟫ₛ = chainInnerProduct c (X.zChainOf g) := by
  rw [NQubitPauliOperator.symplecticInner, ← X.edgeEquiv.sum_comp, chainInnerProduct]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [chainXOperator_operators_edgeEquiv, zChainOf]
  generalize g.operators (X.edgeEquiv e) = P
  obtain h | h := zmod2_eq_zero_or_eq_one (c e) <;> cases P <;>
    simp [h, PauliOperator.symplecticProductSingle]

/-- A Pauli group element `g` commutes with `chainZOperator c` iff the
X-support chain of `g` pairs to `0` with `c`. -/
theorem commutes_chainZOperator_iff (g : NQubitPauliGroupElement X.numQubits)
    (c : X.C1 → ZMod 2) :
    g * X.chainZOperator c = X.chainZOperator c * g ↔
      chainInnerProduct (X.xChainOf g) c = 0 := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero,
    symplecticInner_chainZOperator_right]

/-- `chainXOperator c` commutes with a Pauli group element `g` iff `c` pairs to
`0` with the Z-support chain of `g`. -/
theorem chainXOperator_commutes_iff (c : X.C1 → ZMod 2)
    (g : NQubitPauliGroupElement X.numQubits) :
    X.chainXOperator c * g = g * X.chainXOperator c ↔
      chainInnerProduct c (X.zChainOf g) = 0 := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero,
    symplecticInner_chainXOperator_left]

/-- `chainXOperator c` commutes with `chainZOperator c'` iff the chains pair to
`0`. -/
theorem chainXOperator_commutes_chainZOperator_iff (c c' : X.C1 → ZMod 2) :
    X.chainXOperator c * X.chainZOperator c' =
      X.chainZOperator c' * X.chainXOperator c
    ↔ chainInnerProduct c c' = 0 := by
  rw [commutes_chainZOperator_iff, xChainOf_chainXOperator]

/-- An X-check commutes with a Z-check, by the chain-complex law. -/
theorem faceStabOf_commutes_vertexStabOf (f : X.C2) (v : X.C0) :
    X.faceStabOf f * X.vertexStabOf v = X.vertexStabOf v * X.faceStabOf f :=
  (chainXOperator_commutes_chainZOperator_iff _ _).2
    (chainInnerProduct_boundary2_cutMap_eq_zero (X.singleFace f) (X.singleVtx v))

/-- Two X-checks commute, both being X-type. -/
theorem faceStabOf_commutes_faceStabOf (f f' : X.C2) :
    X.faceStabOf f * X.faceStabOf f' = X.faceStabOf f' * X.faceStabOf f :=
  (faceStabOf_isXType f).commute (faceStabOf_isXType f')

/-- Two Z-checks commute, both being Z-type. -/
theorem vertexStabOf_commutes_vertexStabOf (v v' : X.C0) :
    X.vertexStabOf v * X.vertexStabOf v' = X.vertexStabOf v' * X.vertexStabOf v :=
  (vertexStabOf_isZType v).commute (vertexStabOf_isZType v')

/-- Z generators commute with X generators (CSS cross-commutation). -/
theorem ZGenerators_commute_XGenerators :
    ∀ z ∈ X.ZGenerators, ∀ x ∈ X.XGenerators, z * x = x * z := by
  rintro _ ⟨v, rfl⟩ _ ⟨f, rfl⟩
  exact (faceStabOf_commutes_vertexStabOf f v).symm

end HomologicalCode

end Homological
end Stabilizer
end Quantum

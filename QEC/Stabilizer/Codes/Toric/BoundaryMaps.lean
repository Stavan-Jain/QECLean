import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.Chains

/-!
# Boundary maps of the toric chain complex

The `L × L` torus is cellulated by the periodic square lattice. Cells are
labelled by coordinates `(x, y) : Fin L × Fin L`, taken modulo `L`:

* the horizontal edge `EdgeIdx.h x y` joins the vertices `(x, y)` and
  `(next L x, y)`;
* the vertical edge `EdgeIdx.v x y` joins the vertices `(x, y)` and
  `(x, next L y)`;
* the face `(x, y)` is bounded by the edges `h x y`, `h x (next L y)`, `v x y`
  and `v (next L x) y`.

This file defines the resulting maps on `ZMod 2`-chains:

* `toricBoundary2 : C2 L →ₗ[ZMod 2] C1 L`, the boundary of a 2-chain;
* `toricBoundary1 : C1 L →ₗ[ZMod 2] C0 L`, the boundary of a 1-chain;
* `toricVertexCutMap : C0 L →ₗ[ZMod 2] C1 L`, the coboundary of a 0-chain,
  which is the transpose of `toricBoundary1`;

and proves the chain-complex law `toricBoundary_comp_zero`. For `2 ≤ L` the cut
of a vertex and the boundary of a face are sums of four distinct edges
(`toricVertexCutMap_singleVtx_eq_one_iff`,
`toricBoundary2_singleFace_eq_one_iff`).

The scoped notations `∂₂`, `∂₁` and `δ⁰` (scope `ToricChain`) stand for these
three maps. The lattice size stays an explicit argument, as in `∂₁ L c`, and
the declaration names are still the ones to use in `simp` and `unfold`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

section Maps

variable (L : ℕ) [Fact (0 < L)]

/-- The boundary map `∂₂ : C2 → C1`: an edge receives the sum of the values on
the two faces it borders. -/
def toricBoundary2 : C2 L →ₗ[ZMod 2] C1 L where
  toFun f :=
    fun e => match e with
      | EdgeIdx.h x y => f (x, y) + f (x, prev L y)
      | EdgeIdx.v x y => f (x, y) + f (prev L x, y)
  map_add' f g := by
    ext e
    cases e <;> simp [add_add_add_comm]
  map_smul' a f := by
    ext e
    cases e <;> simp [mul_add]

/-- The boundary map `∂₁ : C1 → C0`: a vertex receives the sum of the values on
the four edges incident to it. -/
def toricBoundary1 : C1 L →ₗ[ZMod 2] C0 L where
  toFun c :=
    fun v =>
      c (EdgeIdx.h v.1 v.2) + c (EdgeIdx.h (prev L v.1) v.2) +
      c (EdgeIdx.v v.1 v.2) + c (EdgeIdx.v v.1 (prev L v.2))
  map_add' c d := by
    ext v
    simp only [Pi.add_apply]
    ring
  map_smul' a c := by
    ext v
    simp [mul_add]

/-- The vertex cut map `δ⁰ : C0 → C1`: an edge receives the sum of the values
at its two endpoints. It is the transpose of `toricBoundary1`. -/
def toricVertexCutMap : C0 L →ₗ[ZMod 2] C1 L where
  toFun s :=
    fun e => match e with
      | EdgeIdx.h x y => s (x, y) + s (next L x, y)
      | EdgeIdx.v x y => s (x, y) + s (x, next L y)
  map_add' s t := by
    ext e
    cases e <;> simp [add_add_add_comm]
  map_smul' a s := by
    ext e
    cases e <;> simp [mul_add]

/-- `∂₂` is the toric face-boundary map `toricBoundary2 : C2 L →ₗ[ZMod 2] C1 L`,
with the lattice size explicit: `∂₂ L f`. Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "∂₂" => Quantum.Stabilizer.Lattice.toricBoundary2

/-- `∂₁` is the toric edge-boundary map `toricBoundary1 : C1 L →ₗ[ZMod 2] C0 L`,
with the lattice size explicit: `∂₁ L c`. Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "∂₁" => Quantum.Stabilizer.Lattice.toricBoundary1

/-- `δ⁰` is the toric vertex cut map `toricVertexCutMap : C0 L →ₗ[ZMod 2] C1 L`,
with the lattice size explicit: `δ⁰ L s`. Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "δ⁰" => Quantum.Stabilizer.Lattice.toricVertexCutMap

open scoped ToricChain

/-! ## Evaluation -/

lemma toricBoundary2_apply_h (f : C2 L) (x y : Fin L) :
    ∂₂ L f (EdgeIdx.h x y) = f (x, y) + f (x, prev L y) := rfl

lemma toricBoundary2_apply_v (f : C2 L) (x y : Fin L) :
    ∂₂ L f (EdgeIdx.v x y) = f (x, y) + f (prev L x, y) := rfl

lemma toricBoundary1_apply (c : C1 L) (v : VtxIdx L) :
    ∂₁ L c v =
      c (EdgeIdx.h v.1 v.2) + c (EdgeIdx.h (prev L v.1) v.2) +
      c (EdgeIdx.v v.1 v.2) + c (EdgeIdx.v v.1 (prev L v.2)) := rfl

lemma toricVertexCutMap_apply_h (s : C0 L) (x y : Fin L) :
    δ⁰ L s (EdgeIdx.h x y) = s (x, y) + s (next L x, y) := rfl

lemma toricVertexCutMap_apply_v (s : C0 L) (x y : Fin L) :
    δ⁰ L s (EdgeIdx.v x y) = s (x, y) + s (x, next L y) := rfl

@[simp] lemma toricBoundary2_singleFace_apply_h (x y x' y' : Fin L) :
    ∂₂ L (singleFace (x, y)) (EdgeIdx.h x' y') =
      (if (x', y') = (x, y) then (1 : ZMod 2) else 0) +
      (if (x', prev L y') = (x, y) then (1 : ZMod 2) else 0) := rfl

@[simp] lemma toricBoundary2_singleFace_apply_v (x y x' y' : Fin L) :
    ∂₂ L (singleFace (x, y)) (EdgeIdx.v x' y') =
      (if (x', y') = (x, y) then (1 : ZMod 2) else 0) +
      (if (prev L x', y') = (x, y) then (1 : ZMod 2) else 0) := rfl

@[simp] lemma toricBoundary1_singleEdge_apply (e : EdgeIdx L) (v : VtxIdx L) :
    ∂₁ L (singleEdge e) v =
      singleEdge e (EdgeIdx.h v.1 v.2) +
      singleEdge e (EdgeIdx.h (prev L v.1) v.2) +
      singleEdge e (EdgeIdx.v v.1 v.2) +
      singleEdge e (EdgeIdx.v v.1 (prev L v.2)) := rfl

/-! ## The chain-complex law -/

/-- The chain-complex law `∂₁ ∘ ∂₂ = 0`: each of the four faces around a vertex
is counted twice. -/
theorem toricBoundary_comp_zero : (∂₁ L).comp (∂₂ L) = 0 := by
  have key : ∀ a b c d : ZMod 2, a + b + (c + d) + (a + c) + (b + d) = 0 := by decide
  ext f v
  exact key _ _ _ _

/-- Pointwise form of `toricBoundary_comp_zero`. -/
theorem toricBoundary_comp_zero_apply (f : C2 L) : ∂₁ L (∂₂ L f) = 0 :=
  LinearMap.congr_fun (toricBoundary_comp_zero L) f

end Maps

/-! ## The cut of a vertex and the boundary of a face -/

section Indicator

open scoped ToricChain

variable (L : ℕ) [Fact (2 ≤ L)]

/-- For `2 ≤ L`, the cut of the vertex `(x, y)` is the sum of the four edges
incident to it. -/
lemma toricVertexCutMap_singleVtx_eq_one_iff (x y : Fin L) (e : EdgeIdx L) :
    δ⁰ L (singleVtx (x, y)) e = 1 ↔
      e = EdgeIdx.h x y ∨ e = EdgeIdx.h (prev L x) y ∨
        e = EdgeIdx.v x y ∨ e = EdgeIdx.v x (prev L y) := by
  have hx := next_ne_self L x
  have hy := next_ne_self L y
  rcases e with ⟨a, b⟩ | ⟨a, b⟩
  · by_cases h1 : a = x <;> by_cases h2 : next L a = x <;> by_cases h3 : b = y <;>
      simp_all [toricVertexCutMap_apply_h, singleVtx]
  · by_cases h1 : b = y <;> by_cases h2 : next L b = y <;> by_cases h3 : a = x <;>
      simp_all [toricVertexCutMap_apply_v, singleVtx]

/-- For `2 ≤ L`, the boundary of the face `(x, y)` is the sum of the four edges
around it. -/
lemma toricBoundary2_singleFace_eq_one_iff (x y : Fin L) (e : EdgeIdx L) :
    ∂₂ L (singleFace (x, y)) e = 1 ↔
      e = EdgeIdx.h x y ∨ e = EdgeIdx.h x (next L y) ∨
        e = EdgeIdx.v x y ∨ e = EdgeIdx.v (next L x) y := by
  have hx := prev_ne_self L x
  have hy := prev_ne_self L y
  rcases e with ⟨a, b⟩ | ⟨a, b⟩
  · by_cases h1 : b = y <;> by_cases h2 : prev L b = y <;> by_cases h3 : a = x <;>
      simp_all [toricBoundary2_apply_h, singleFace]
  · by_cases h1 : a = x <;> by_cases h2 : prev L a = x <;> by_cases h3 : b = y <;>
      simp_all [toricBoundary2_apply_v, singleFace]

end Indicator

end Lattice
end Stabilizer
end Quantum

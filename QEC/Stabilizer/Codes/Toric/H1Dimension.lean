import QEC.Stabilizer.Framework.Homological.ToCode
import QEC.Stabilizer.Codes.Toric.ChainComplex

/-!
# The toric code encodes two qubits: `dim H₁ = 2`

The dimension count for the toric chain complex over `ZMod 2`.

* The torus is connected, so a 0-chain with zero cut is constant
  (`mem_ker_cutMap_iff`) and a 2-chain with zero boundary is constant
  (`mem_ker_boundary2_iff`): both kernels are one-dimensional.
* By rank-nullity and equality of the ranks of `∂₁` and its transpose `δ⁰`,
  `dim Z₁ = L² + 1` (`toric_finrank_cycles`) and `dim B₁ = L² - 1`
  (`toric_finrank_boundaries`).
* Hence `dim H₁ = 2` (`toric_finrank_H1_eq_two`).

The connectivity argument rests on `eq_of_forall_next_eq₂`: a function on
`Fin L × Fin L` that is invariant under the cyclic successor in each coordinate
is constant.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped Homology
open scoped ToricChain
open Homological

variable (L : ℕ) [Fact (0 < L)]

/-! ## The kernels of `δ⁰` and `∂₂` -/

/-- A submodule of `ι → ZMod 2` consisting of the constant functions is
one-dimensional. -/
private lemma finrank_eq_one_of_mem_iff_const {ι : Type*} [Nonempty ι]
    (K : Submodule (ZMod 2) (ι → ZMod 2))
    (hK : ∀ s, s ∈ K ↔ ∃ c : ZMod 2, s = fun _ => c) : dim₂ K = 1 := by
  have hspan : K = Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
    ext s
    rw [hK, Submodule.mem_span_singleton]
    exact exists_congr fun c => ⟨fun h => h ▸ by ext; simp, fun h => h ▸ by ext; simp⟩
  rw [hspan, finrank_span_singleton]
  exact fun h => one_ne_zero (congrFun h (Classical.arbitrary ι))

/-- The kernel of the vertex cut map consists of the constant 0-chains. -/
theorem mem_ker_cutMap_iff (s : C0 L) :
    s ∈ LinearMap.ker (δ⁰ L) ↔ ∃ c : ZMod 2, s = fun _ => c := by
  refine ⟨fun hs => ?_, ?_⟩
  · have hx : ∀ x y, s (next L x, y) = s (x, y) := fun x y =>
      (CharTwo.add_eq_zero.1 (congrFun hs (EdgeIdx.h x y))).symm
    have hy : ∀ x y, s (x, next L y) = s (x, y) := fun x y =>
      (CharTwo.add_eq_zero.1 (congrFun hs (EdgeIdx.v x y))).symm
    exact ⟨s (zeroCoord L, zeroCoord L), funext fun p => eq_of_forall_next_eq₂ L s hx hy p _⟩
  · rintro ⟨c, rfl⟩
    ext e
    cases e <;> exact CharTwo.add_self_eq_zero c

/-- The kernel of `∂₂` consists of the constant 2-chains. -/
theorem mem_ker_boundary2_iff (f : C2 L) :
    f ∈ LinearMap.ker (∂₂ L) ↔ ∃ c : ZMod 2, f = fun _ => c := by
  refine ⟨fun hf => ?_, ?_⟩
  · have hx : ∀ x y, f (next L x, y) = f (x, y) := fun x y => by
      have h := congrFun hf (EdgeIdx.v (next L x) y)
      rw [toricBoundary2_apply_v, prev_next] at h
      exact CharTwo.add_eq_zero.1 h
    have hy : ∀ x y, f (x, next L y) = f (x, y) := fun x y => by
      have h := congrFun hf (EdgeIdx.h x (next L y))
      rw [toricBoundary2_apply_h, prev_next] at h
      exact CharTwo.add_eq_zero.1 h
    exact ⟨f (zeroCoord L, zeroCoord L), funext fun p => eq_of_forall_next_eq₂ L f hx hy p _⟩
  · rintro ⟨c, rfl⟩
    ext e
    cases e <;> exact CharTwo.add_self_eq_zero c

/-- The kernel of the vertex cut map is one-dimensional. -/
theorem toric_finrank_ker_cutMap_eq_one : dim₂ (LinearMap.ker (δ⁰ L)) = 1 :=
  have : Nonempty (VtxIdx L) := ⟨(zeroCoord L, zeroCoord L)⟩
  finrank_eq_one_of_mem_iff_const _ (mem_ker_cutMap_iff L)

/-- The kernel of `∂₂` is one-dimensional. -/
theorem toric_finrank_ker_boundary2_eq_one : dim₂ (LinearMap.ker (∂₂ L)) = 1 :=
  have : Nonempty (FaceIdx L) := ⟨(zeroCoord L, zeroCoord L)⟩
  finrank_eq_one_of_mem_iff_const _ (mem_ker_boundary2_iff L)

/-! ## Dimensions of cycles, boundaries and homology -/

/-- `∂₁` and its transpose `δ⁰` have the same rank. -/
theorem toric_rank_boundary1_eq_rank_cutMap :
    dim₂ (LinearMap.range (∂₁ L)) = dim₂ (LinearMap.range (δ⁰ L)) := by
  rw [← toricHomologicalCode_cutMap_eq]
  exact (toricHomologicalCode L).finrank_range_cutMap.symm

/-- The rank of `∂₁` is `L² - 1`. -/
theorem toric_rank_boundary1 : dim₂ (LinearMap.range (∂₁ L)) = L * L - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (δ⁰ L)
  rw [toric_finrank_ker_cutMap_eq_one, Module.finrank_fintype_fun_eq_card, card_vtxIdx] at h
  rw [toric_rank_boundary1_eq_rank_cutMap]
  omega

/-- The cycle space has dimension `L² + 1`. -/
theorem toric_finrank_cycles : dim₂ (Z₁ L) = L * L + 1 := by
  have h : dim₂ (LinearMap.range (∂₁ L)) + dim₂ (Z₁ L) = dim₂ (C1 L) :=
    LinearMap.finrank_range_add_finrank_ker (∂₁ L)
  have hL : 0 < L * L := Nat.mul_pos Fact.out Fact.out
  rw [toric_rank_boundary1, Module.finrank_fintype_fun_eq_card, card_edgeIdx, Nat.mul_assoc] at h
  omega

/-- The boundary space has dimension `L² - 1`. -/
theorem toric_finrank_boundaries : dim₂ (B₁ L) = L * L - 1 := by
  have h : dim₂ (B₁ L) + dim₂ (LinearMap.ker (∂₂ L)) = dim₂ (C2 L) :=
    LinearMap.finrank_range_add_finrank_ker (∂₂ L)
  rw [toric_finrank_ker_boundary2_eq_one, Module.finrank_fintype_fun_eq_card, card_faceIdx] at h
  omega

/-- The first homology of the toric chain complex is two-dimensional:
`dim H₁ = dim Z₁ - dim B₁ = (L² + 1) - (L² - 1) = 2`. -/
theorem toric_finrank_H1_eq_two : dim₂ (H₁ L) = 2 := by
  have h : dim₂ (H₁ L) = dim₂ (Z₁ L) - dim₂ (B₁ L) :=
    (toricHomologicalCode L).finrank_H1_eq_cycles_sub_boundaries
  have hL : 0 < L * L := Nat.mul_pos Fact.out Fact.out
  rw [toric_finrank_cycles, toric_finrank_boundaries] at h
  omega

end Lattice
end Stabilizer
end Quantum

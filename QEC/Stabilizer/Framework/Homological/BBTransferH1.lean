import QEC.Stabilizer.Framework.Homological.BBCover
import QEC.Stabilizer.Framework.Homological.BBBocksteinRank

/-!
# The transfer maps on `H₁` of a double cover

Let `D : XDoubleCoverData G H` be a free double cover of bivariate bicycle
codes, with pushforward `p = push1`, pullback `τ = pull1` and deck translation
`σ` on 1-chains. Both `p` and `τ` are chain maps, so they induce maps `p_*` and
`τ_*` between the first homology groups `H₁ = cycles / boundaries` of the cover
and of the base. Write `k̃ = dim H₁(cover)` and `k = dim H₁(base)` for the
numbers of logical qubits of the two codes.

## Main definitions

* `push1Cycles`, `pull1Cycles`: `p` and `τ` restricted to 1-cycles.
* `pushH1 : H₁(cover) → H₁(base)` and `pullH1 : H₁(base) → H₁(cover)`: the
  induced maps `p_*` and `τ_*`.
* `epsH1 = τ_* ∘ p_*`: the endomorphism `ε_*` of `H₁(cover)`. It is induced
  by `1 + σ`, since `τ (p v) = v + σ v` (`pull1_push1`).
* `BocksteinVanishes`: the condition `ker τ_* ≤ range p_*`. In the long exact
  homology sequence of `0 → C(base) → C(cover) → C(base) → 0`, with maps `τ`
  and `p`, it says that the composite `H₂ → H₁ → H₀` of the two connecting maps
  of the base vanishes.

## Main statements

* `ker_pushH1_eq_range_pullH1`: the sequence is exact at the cover,
  `ker p_* = range τ_*`.
* `finrank_H1_sub_le_finrank_range_epsH1`: `k̃ - k ≤ dim (range ε_*)`.
* `finrank_range_epsH1_add_eq`, `finrank_range_epsH1_eq`,
  `finrank_ker_epsH1_eq`: under `BocksteinVanishes`,
  `dim (range ε_*) + k = k̃` and `dim (ker ε_*) = k`.
* `epsH1_epsH1_apply`: `ε_* ∘ ε_* = 0`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped Homology

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The transfer maps on 1-cycles -/

/-- The pushforward `p` restricted to 1-cycles. -/
noncomputable def push1Cycles :
    D.coverComplex.cycles →ₗ[ZMod 2] D.baseComplex.cycles :=
  D.push1.restrict fun _ hv => D.push1_mem_cycles hv

/-- The pullback `τ` restricted to 1-cycles. -/
noncomputable def pull1Cycles :
    D.baseComplex.cycles →ₗ[ZMod 2] D.coverComplex.cycles :=
  D.pull1.restrict fun _ hu => D.pull1_mem_cycles hu

@[simp] lemma coe_push1Cycles (v : D.coverComplex.cycles) :
    (D.push1Cycles v : D.baseComplex.C1 → ZMod 2)
      = D.push1 (v : D.coverComplex.C1 → ZMod 2) := rfl

@[simp] lemma coe_pull1Cycles (u : D.baseComplex.cycles) :
    (D.pull1Cycles u : D.coverComplex.C1 → ZMod 2)
      = D.pull1 (u : D.baseComplex.C1 → ZMod 2) := rfl

/-- On cycles, `p ∘ τ = 0`. -/
lemma push1Cycles_pull1Cycles (u : D.baseComplex.cycles) :
    D.push1Cycles (D.pull1Cycles u) = 0 :=
  Subtype.ext (D.push1_pull1_eq_zero u.1)

/-! ## The induced maps on `H₁` -/

/-- The pushforward `p_* : H₁(cover) → H₁(base)` on homology. -/
noncomputable def pushH1 :
    D.coverComplex.H1 →ₗ[ZMod 2] D.baseComplex.H1 :=
  Submodule.mapQ _ _ D.push1Cycles fun _ hv => D.push1_mem_boundaries hv

/-- The pullback `τ_* : H₁(base) → H₁(cover)` on homology. -/
noncomputable def pullH1 :
    D.baseComplex.H1 →ₗ[ZMod 2] D.coverComplex.H1 :=
  Submodule.mapQ _ _ D.pull1Cycles fun _ hu => D.pull1_mem_boundaries hu

lemma pushH1_mk (v : D.coverComplex.cycles) :
    D.pushH1 (Submodule.Quotient.mk v)
      = Submodule.Quotient.mk (D.push1Cycles v) := rfl

lemma pullH1_mk (u : D.baseComplex.cycles) :
    D.pullH1 (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (D.pull1Cycles u) := rfl

/-- `p_* ∘ τ_* = 0` on `H₁`. -/
lemma pushH1_pullH1 (y : D.baseComplex.H1) : D.pushH1 (D.pullH1 y) = 0 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [pullH1_mk, pushH1_mk, push1Cycles_pull1Cycles, Submodule.Quotient.mk_zero]

/-! ## Exactness at the cover -/

/-- `ker p_* ≤ range τ_*`: a cover cycle whose pushforward is a base boundary
differs from the pullback of a base cycle by a cover boundary
(`exists_pull_eq_add_boundary`). -/
theorem ker_pushH1_le_range_pullH1 :
    LinearMap.ker D.pushH1 ≤ LinearMap.range D.pullH1 := by
  intro x hx
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hbd : D.push1Cycles ⟨v, hv⟩ ∈ D.baseComplex.boundarySubmoduleInCycles :=
    (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx)
  obtain ⟨u, hu, f, hf⟩ := D.exists_pull_eq_add_boundary hv hbd
  refine ⟨Submodule.Quotient.mk ⟨u, hu⟩, (Submodule.Quotient.eq _).mpr ?_⟩
  change ((D.pull1Cycles ⟨u, hu⟩ - ⟨v, hv⟩ : D.coverComplex.cycles) :
      D.coverComplex.C1 → ZMod 2) ∈ D.coverComplex.boundaries
  exact ⟨f, eq_sub_of_add_eq' hf.symm⟩

/-- The transfer sequence is exact at the cover: `ker p_* = range τ_*` on
`H₁`. -/
theorem ker_pushH1_eq_range_pullH1 :
    LinearMap.ker D.pushH1 = LinearMap.range D.pullH1 :=
  le_antisymm D.ker_pushH1_le_range_pullH1
    (LinearMap.range_le_ker_iff.mpr (LinearMap.ext D.pushH1_pullH1))

/-! ## The deck endomorphism of `H₁` -/

/-- The endomorphism `ε_* = τ_* ∘ p_*` of `H₁(cover)`. It sends the class of
a cycle `v` to the class of `τ (p v) = v + σ v` (`epsH1_mk`, `pull1_push1`). -/
noncomputable def epsH1 :
    D.coverComplex.H1 →ₗ[ZMod 2] D.coverComplex.H1 :=
  D.pullH1 ∘ₗ D.pushH1

lemma epsH1_mk (v : D.coverComplex.cycles) :
    D.epsH1 (Submodule.Quotient.mk v)
      = Submodule.Quotient.mk (D.pull1Cycles (D.push1Cycles v)) := rfl

/-- `ε_* ∘ ε_* = 0` on `H₁(cover)`, because `p_* ∘ τ_* = 0`. This reflects
`(1 + σ)² = 1 + σ² = 0` in characteristic 2, and makes `H₁(cover)` a module over
`𝔽₂[ε]/(ε²)`. -/
theorem epsH1_epsH1_apply (x : D.coverComplex.H1) :
    D.epsH1 (D.epsH1 x) = 0 := by
  simp only [epsH1, LinearMap.comp_apply, pushH1_pullH1, map_zero]

/-- `k̃ - k ≤ dim (range ε_*)`: the image of `1 + σ` on `H₁(cover)` has
dimension at least `dim H₁(cover) - dim H₁(base)`. -/
theorem finrank_H1_sub_le_finrank_range_epsH1 :
    dim₂ D.coverComplex.H1
      - dim₂ D.baseComplex.H1
      ≤ dim₂ (LinearMap.range D.epsH1) :=
  BBBocksteinRank.finrank_sub_le_finrank_range_comp D.pushH1 D.pullH1
    D.ker_pushH1_eq_range_pullH1

/-! ## Equality under the Bockstein-vanishing criterion -/

/-- The Bockstein-vanishing criterion: `ker τ_* ≤ range p_*` on `H₁`. The
kernel of `τ_*` is the image of the connecting map `H₂(base) → H₁(base)` and
the image of `p_*` is the kernel of the connecting map `H₁(base) → H₀(base)`,
so the criterion says that the composite of the two connecting maps vanishes.
It is the hypothesis under which the bound `k̃ - k ≤ dim (range ε_*)` is an
equality. -/
def BocksteinVanishes : Prop :=
  LinearMap.ker D.pullH1 ≤ LinearMap.range D.pushH1

/-- Under `BocksteinVanishes`, `dim (range ε_*) + k = k̃`. In particular
`k ≤ k̃`. -/
theorem finrank_range_epsH1_add_eq (h : D.BocksteinVanishes) :
    dim₂ (LinearMap.range D.epsH1)
        + dim₂ D.baseComplex.H1
      = dim₂ D.coverComplex.H1 :=
  BBBocksteinRank.finrank_range_comp_add_eq_of_ker_le D.pushH1 D.pullH1
    D.ker_pushH1_eq_range_pullH1 h

/-- Under `BocksteinVanishes`, `dim (range ε_*) = k̃ - k`. -/
theorem finrank_range_epsH1_eq (h : D.BocksteinVanishes) :
    dim₂ (LinearMap.range D.epsH1)
      = dim₂ D.coverComplex.H1
        - dim₂ D.baseComplex.H1 :=
  BBBocksteinRank.finrank_range_comp_eq_of_ker_le D.pushH1 D.pullH1
    D.ker_pushH1_eq_range_pullH1 h

/-- Under `BocksteinVanishes`, `dim (ker ε_*) = k`, by rank–nullity for
`ε_*`. -/
theorem finrank_ker_epsH1_eq (h : D.BocksteinVanishes) :
    dim₂ (LinearMap.ker D.epsH1)
      = dim₂ D.baseComplex.H1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker D.epsH1
  have hadd := D.finrank_range_epsH1_add_eq h
  omega

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum

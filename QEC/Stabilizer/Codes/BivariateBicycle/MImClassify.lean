/-
# Phase 6: discharging `MImBound` — the safe-sector confined-frame floor

`MImBound` (`SafeSector.lean`, A4 Part II / Theorem D) is the last assumed `Prop`
for an unconditional `d(gross) = 12`: every base 1-cycle in a nonzero Smith class
`[seamC ζ]` (`ζ ∈ ker ∂₂`) has weight ≥ 12.  The paper proof is the confined-frame
collapse of A4 §§9–13; this module formalizes it, reusing the CRT frame
(`CRTFrame.lean`) and the layer/Fourier machinery built for the dangerous sector
(`LightStab.lean`).

## Structure

* **§0 weight join** — `chainWeight w = bwt (leftHalf w) + bwt (rightHalf w)`
  and its layer-sum corollary, bridging the noncomputable `bb72Complex.chainWeight`
  to the per-block, per-`Z₂²`-layer `weight3 (slice …)` decomposition that the
  CRT frame bounds.  (This is the "join" the route hinges on; it is structural,
  not a research item, because `seamC ζ + ∂₂ f` is a base 1-chain and `weight_bridge`
  already decomposes a block over its `Z₂²` layers.)

## Convention bridge (lab notes → repo)

Repo `∂₂ f = (A⋆f | B⋆f)`: A-block at `j = 0`, B-block at `j = 1`.
**Repo-left = lab-right** (every "lighter block" reference in A4 §§9–14 flips).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.LightStab

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

open scoped BigOperators

-- The seam/lift defeq chains unfold deep `Prod`/`ZMod` instance towers.
set_option maxRecDepth 4096

/-! ## §0 The weight join: `chainWeight` as a sum of per-block layer weights -/

/-- **Block split of the chain weight.**  A base 1-chain's weight is the sum of its
two blocks' weights (the `h ↦ (h,0)` / `h ↦ (h,1)` images partition the support). -/
theorem chainWeight_eq_bwt_blocks (w : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight w = bwt (leftHalf w) + bwt (rightHalf w) := by
  rw [bb72Complex_chainWeight_eq]
  unfold bwt
  have hz : ∀ a : ZMod 2, (a ≠ 0) ↔ (a = 1) := by decide
  have injA : Function.Injective (fun h : BaseGroup => (h, (0 : Fin 2))) :=
    fun a b h => (Prod.mk.injEq ..).mp h |>.1
  have injB : Function.Injective (fun h : BaseGroup => (h, (1 : Fin 2))) :=
    fun a b h => (Prod.mk.injEq ..).mp h |>.1
  rw [← Finset.card_image_of_injective _ injA, ← Finset.card_image_of_injective _ injB,
    ← Finset.card_union_of_disjoint ?_]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro hp
      rcases p with ⟨h, j⟩
      fin_cases j
      · exact Or.inl ⟨h, (hz _).mp hp, rfl⟩
      · exact Or.inr ⟨h, (hz _).mp hp, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact (hz _).mpr ha
      · exact (hz _).mpr ha
  · rw [Finset.disjoint_left]
    intro p hpa hpb
    simp only [Finset.mem_image, Finset.mem_filter] at hpa hpb
    obtain ⟨a, _, rfl⟩ := hpa
    obtain ⟨b, _, hb⟩ := hpb
    exact absurd ((Prod.mk.injEq ..).mp hb).2 (by decide)

/-- **The layer-sum decomposition of the chain weight.**  Composes the block split
with the per-block `Z₂²`-layer decomposition `weight_bridge`.  This is the form the
A4 §10 slot frame bounds: each summand is the weight of a `Z₃²`-torus slice. -/
theorem chainWeight_eq_layer_sum (w : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight w
      = (∑ s : ZMod 2 × ZMod 2, weight3 (slice (leftHalf w) s))
        + (∑ s : ZMod 2 × ZMod 2, weight3 (slice (rightHalf w) s)) := by
  rw [chainWeight_eq_bwt_blocks, weight_bridge, weight_bridge]

/-! ## §1 Parity: every Smith-coset element has even weight

The coset element `seamC ζ + ∂₂ f` is a base 1-cycle (`seamC_mem_cycles` puts
`seamC ζ` in cycles; `∂₂ f` is a boundary, hence a cycle), so it has even weight
(A4 §9.3 (PAR)).  Combined with the §§11–13 floor of ≥ 10 and the §13 kill of the
weight-10 achievers, evenness lifts the bound to ≥ 12 on the wt-16/18 orbits. -/

/-- Every Smith-coset element is a base 1-cycle, hence has even chain weight. -/
theorem coset_weight_even (ζ f : BaseGroup → ZMod 2)
    (hζ : bbBoundary2Fn baseA baseB ζ = 0) :
    Even (bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f)) := by
  have hbd : bbBoundary2Fn baseA baseB f ∈ bb72Complex.boundaries := ⟨f, rfl⟩
  have hcyc : seamC ζ + bbBoundary2Fn baseA baseB f ∈ bb72Complex.cycles :=
    Submodule.add_mem _ (seamC_mem_cycles hζ) (bb72Complex.boundaries_le_cycles hbd)
  rw [bb72Complex_chainWeight_eq, Nat.even_iff]
  exact cycle_weight_even _ hcyc

/-! ## §2 The `ker ∂₂` basis and M-VANISH on the basis (A4 §9.4)

`ker ∂₂ = {ζ : conv baseA ζ = 0 ∧ conv baseB ζ = 0}` is 6-dimensional (64
elements, 63 nonzero in 5 translation orbits of weights 16/18/18/24/24 — matching
A4 §9.3).  We pin a basis and verify, by `native_decide`, that the CRT
components 0 and 2 of `seamC` vanish on each basis vector (A4 §9.4 Sharpening 1:
`off₀ = off₂ = 0`).  Since `V ψⱼ s ∘ leftHalf ∘ seamC` is F₂-linear in `ζ`, this
extends to all of `ker ∂₂` once the basis is shown to span it (§2 spanning, todo). -/

/-- Indicator of a finite support set. -/
def mkZeta (supp : List BaseGroup) : BaseGroup → ZMod 2 := fun h => if h ∈ supp then 1 else 0

/-- The four `Z₂²` layers (slots). -/
def slots4 : List (ZMod 2 × ZMod 2) := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- A basis of `ker ∂₂` (GF(2) nullspace of `[conv baseA ; conv baseB]`). -/
def kerBasis : List (BaseGroup → ZMod 2) :=
  [ mkZeta [(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),
            (3,0),(3,1),(3,3),(3,4),(4,0),(4,1),(4,3),(4,4)],
    mkZeta [(0,0),(0,2),(0,3),(0,5),(1,0),(1,2),(1,3),(1,5),
            (3,0),(3,2),(3,3),(3,5),(4,0),(4,2),(4,3),(4,5)],
    mkZeta [(0,0),(0,4),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),
            (3,1),(3,2),(3,5),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],
    mkZeta [(0,0),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2),
            (2,3),(2,4),(2,5),(3,2),(3,4),(4,0),(4,2),(5,1),(5,3)],
    mkZeta [(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),
            (2,5),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0),(5,4)],
    mkZeta [(0,0),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),
            (2,3),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3),(5,1),(5,5)] ]

/-- Each basis vector lies in `ker ∂₂`. -/
theorem kerBasis_mem :
    kerBasis.all (fun v => decide (bbBoundary2Fn baseA baseB v = 0)) = true := by
  native_decide

/-- The components-0 and -2 of `seamC` (both blocks) vanish for a chain. -/
def offVanishes (v : BaseGroup → ZMod 2) : Bool :=
  slots4.all (fun s => decide (V psi0 s (leftHalf (seamC v)) = 0)) &&
  slots4.all (fun s => decide (V psi0 s (rightHalf (seamC v)) = 0)) &&
  slots4.all (fun s => decide (V psi2 s (leftHalf (seamC v)) = 0)) &&
  slots4.all (fun s => decide (V psi2 s (rightHalf (seamC v)) = 0))

/-- **M-VANISH on the basis** (A4 §9.4 Sharpening 1): `off₀ = off₂ = 0` for each
`ker ∂₂` basis vector.  By F₂-linearity of `V ψⱼ s ∘ leftHalf ∘ seamC`, this
extends to all of `ker ∂₂`. -/
theorem mvanish_basis : kerBasis.all offVanishes = true := by
  native_decide

end Quantum.Stabilizer.Homological.BB.LightStab

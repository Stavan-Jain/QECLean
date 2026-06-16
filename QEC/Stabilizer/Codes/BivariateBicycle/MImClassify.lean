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
import QEC.Stabilizer.Codes.BivariateBicycle.LightStabClassify

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

/-! ## §2 The `ker ∂₂` basis, spanning, and M-VANISH (A4 §9.3–§9.4)

`ker ∂₂ = {ζ : conv baseA ζ = 0 ∧ conv baseB ζ = 0}` is 6-dimensional (64 elements,
63 nonzero in 5 translation orbits of weights 16/18/18/24/24 — matching A4 §9.3).  We
pin a systematic basis `kb0..kb5` (with `kbᵢ` supported so that `kbᵢ(freeCellⱼ) = δᵢⱼ`),
prove it spans `ker ∂₂` (every `ζ ∈ ker ∂₂` is reconstructed from its 6 free-cell
coordinates, `kerBasis_spans`), and deduce A4 §9.4 Sharpening 1 — the CRT components 0
and 2 of `seamC ζ` vanish (`off_vanish`) — by a `native_decide` over the 64 combinations. -/

/-- Indicator of a finite support set. -/
def mkZeta (supp : List BaseGroup) : BaseGroup → ZMod 2 := fun h => if h ∈ supp then 1 else 0

def kb0 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),
          (3,0),(3,1),(3,3),(3,4),(4,0),(4,1),(4,3),(4,4)]
def kb1 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,2),(0,3),(0,5),(1,0),(1,2),(1,3),(1,5),
          (3,0),(3,2),(3,3),(3,5),(4,0),(4,2),(4,3),(4,5)]
def kb2 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,4),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),
          (3,1),(3,2),(3,5),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)]
def kb3 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2),
          (2,3),(2,4),(2,5),(3,2),(3,4),(4,0),(4,2),(5,1),(5,3)]
def kb4 : BaseGroup → ZMod 2 :=
  mkZeta [(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),
          (2,5),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0),(5,4)]
def kb5 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),
          (2,3),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3),(5,1),(5,5)]

def freeCells : List BaseGroup := [(4,4),(4,5),(5,2),(5,3),(5,4),(5,5)]

-- 324 (out, in, block) factorization entries
def cPairs : List (BaseGroup × BaseGroup × Fin 2) :=
  [((0,0),((0,0),0)),((0,0),((0,5),0)),((0,0),((1,2),0)),((0,0),((1,5),0)),((0,0),((2,0),0)),
   ((0,0),((2,1),0)),((0,0),((2,3),0)),((0,0),((2,4),0)),((0,0),((2,5),0)),((0,0),((3,1),0)),
   ((0,0),((4,0),0)),((0,0),((4,1),0)),((0,0),((5,0),0)),((0,0),((5,1),0)),((0,0),((0,0),1)),
   ((0,0),((0,2),1)),((0,0),((1,0),1)),((0,0),((1,1),1)),((0,1),((0,0),0)),((0,1),((0,5),0)),
   ((0,1),((1,2),0)),((0,1),((2,2),0)),((0,1),((3,1),0)),((0,1),((4,0),0)),((0,1),((4,1),0)),
   ((0,1),((5,0),0)),((0,1),((5,1),0)),((0,1),((0,0),1)),((0,1),((0,2),1)),((0,2),((0,4),0)),
   ((0,2),((0,5),0)),((0,2),((1,0),0)),((0,2),((1,1),0)),((0,2),((1,3),0)),((0,2),((1,4),0)),
   ((0,2),((1,5),0)),((0,2),((2,0),0)),((0,2),((2,1),0)),((0,2),((2,3),0)),((0,2),((2,4),0)),
   ((0,2),((2,5),0)),((0,2),((3,0),0)),((0,2),((4,0),0)),((0,2),((4,1),0)),((0,2),((5,0),0)),
   ((0,2),((5,1),0)),((0,2),((0,1),1)),((0,2),((0,3),1)),((0,3),((1,3),0)),((0,3),((1,4),0)),
   ((0,3),((4,1),0)),((0,3),((0,0),1)),((0,3),((0,3),1)),((0,3),((1,0),1)),((0,4),((0,0),0)),
   ((0,4),((0,5),0)),((0,4),((1,0),0)),((0,4),((1,1),0)),((0,4),((1,2),0)),((0,4),((1,3),0)),
   ((0,4),((1,4),0)),((0,4),((3,1),0)),((0,4),((0,0),1)),((0,4),((0,1),1)),((0,4),((0,2),1)),
   ((0,4),((0,3),1)),((0,4),((1,0),1)),((0,4),((1,1),1)),((0,5),((1,2),0)),((0,5),((1,3),0)),
   ((0,5),((1,4),0)),((0,5),((2,2),0)),((0,5),((4,0),0)),((0,5),((5,0),0)),((0,5),((5,1),0)),
   ((0,5),((0,2),1)),((0,5),((0,3),1)),((0,5),((1,0),1)),((1,0),((4,0),0)),((1,1),((1,3),0)),
   ((1,1),((1,4),0)),((1,1),((2,2),0)),((1,1),((5,0),0)),((1,1),((5,1),0)),((1,1),((0,3),1)),
   ((1,1),((1,0),1)),((1,2),((0,0),0)),((1,2),((0,5),0)),((1,2),((1,2),0)),((1,2),((1,4),0)),
   ((1,2),((1,5),0)),((1,2),((2,0),0)),((1,2),((2,1),0)),((1,2),((2,2),0)),((1,2),((2,3),0)),
   ((1,2),((2,4),0)),((1,2),((2,5),0)),((1,2),((3,1),0)),((1,2),((4,0),0)),((1,2),((4,1),0)),
   ((1,2),((0,0),1)),((1,2),((0,2),1)),((1,2),((1,1),1)),((1,3),((0,0),0)),((1,3),((0,5),0)),
   ((1,3),((1,2),0)),((1,3),((1,5),0)),((1,3),((2,0),0)),((1,3),((2,1),0)),((1,3),((2,2),0)),
   ((1,3),((2,3),0)),((1,3),((2,4),0)),((1,3),((2,5),0)),((1,3),((3,1),0)),((1,3),((4,0),0)),
   ((1,3),((4,1),0)),((1,3),((0,0),1)),((1,3),((0,2),1)),((1,3),((1,1),1)),((1,4),((0,0),0)),
   ((1,4),((0,5),0)),((1,4),((1,2),0)),((1,4),((2,0),0)),((1,4),((2,1),0)),((1,4),((2,2),0)),
   ((1,4),((2,3),0)),((1,4),((2,4),0)),((1,4),((2,5),0)),((1,4),((3,1),0)),((1,4),((4,0),0)),
   ((1,4),((4,1),0)),((1,4),((0,0),1)),((1,4),((0,2),1)),((1,4),((1,1),1)),((1,5),((0,0),0)),
   ((1,5),((0,5),0)),((1,5),((1,0),0)),((1,5),((1,2),0)),((1,5),((1,3),0)),((1,5),((1,4),0)),
   ((1,5),((2,0),0)),((1,5),((2,1),0)),((1,5),((2,3),0)),((1,5),((2,4),0)),((1,5),((2,5),0)),
   ((1,5),((3,1),0)),((1,5),((4,0),0)),((1,5),((5,0),0)),((1,5),((5,1),0)),((1,5),((0,0),1)),
   ((1,5),((0,2),1)),((1,5),((0,3),1)),((1,5),((1,0),1)),((1,5),((1,1),1)),((2,0),((5,0),0)),
   ((2,1),((2,2),0)),((2,1),((5,0),0)),((2,2),((2,2),0)),((2,2),((2,3),0)),((2,2),((5,0),0)),
   ((2,3),((2,2),0)),((2,3),((2,3),0)),((2,3),((2,4),0)),((2,3),((5,0),0)),((2,4),((2,2),0)),
   ((2,4),((2,3),0)),((2,4),((2,4),0)),((2,4),((2,5),0)),((2,4),((5,0),0)),((2,5),((2,0),0)),
   ((2,5),((2,3),0)),((2,5),((2,4),0)),((2,5),((2,5),0)),((2,5),((5,1),0)),((3,0),((0,5),0)),
   ((3,0),((1,0),0)),((3,0),((1,1),0)),((3,0),((2,2),0)),((3,0),((3,1),0)),((3,0),((4,0),0)),
   ((3,0),((5,0),0)),((3,0),((5,1),0)),((3,0),((0,0),1)),((3,0),((0,1),1)),((3,0),((1,1),1)),
   ((3,1),((0,0),0)),((3,1),((0,1),0)),((3,1),((0,5),0)),((3,1),((1,3),0)),((3,1),((1,4),0)),
   ((3,1),((1,5),0)),((3,1),((2,0),0)),((3,1),((2,1),0)),((3,1),((2,2),0)),((3,1),((2,3),0)),
   ((3,1),((2,4),0)),((3,1),((2,5),0)),((3,1),((3,1),0)),((3,1),((4,1),0)),((3,1),((0,0),1)),
   ((3,1),((0,3),1)),((3,1),((1,1),1)),((3,2),((0,2),0)),((3,2),((1,5),0)),((3,2),((2,0),0)),
   ((3,2),((2,1),0)),((3,2),((2,2),0)),((3,2),((2,3),0)),((3,2),((2,4),0)),((3,2),((2,5),0)),
   ((3,2),((1,0),1)),((3,2),((1,1),1)),((3,3),((0,0),0)),((3,3),((0,3),0)),((3,3),((0,4),0)),
   ((3,3),((1,0),0)),((3,3),((1,1),0)),((3,3),((1,2),0)),((3,3),((1,3),0)),((3,3),((1,4),0)),
   ((3,3),((1,5),0)),((3,3),((2,0),0)),((3,3),((2,1),0)),((3,3),((2,2),0)),((3,3),((2,3),0)),
   ((3,3),((2,4),0)),((3,3),((2,5),0)),((3,3),((3,0),0)),((3,3),((3,1),0)),((3,3),((0,0),1)),
   ((3,3),((0,1),1)),((3,3),((0,2),1)),((3,3),((0,3),1)),((3,4),((0,5),0)),((3,4),((1,0),0)),
   ((3,4),((1,1),0)),((3,4),((1,5),0)),((3,4),((2,0),0)),((3,4),((2,1),0)),((3,4),((2,3),0)),
   ((3,4),((2,4),0)),((3,4),((2,5),0)),((3,4),((3,0),0)),((3,4),((4,0),0)),((3,4),((5,0),0)),
   ((3,4),((5,1),0)),((3,4),((0,0),1)),((3,4),((0,1),1)),((3,4),((1,0),1)),((3,5),((0,0),0)),
   ((3,5),((1,0),0)),((3,5),((1,1),0)),((3,5),((1,2),0)),((3,5),((3,1),0)),((3,5),((4,1),0)),
   ((3,5),((0,1),1)),((3,5),((0,2),1)),((3,5),((1,1),1)),((4,0),((1,3),0)),((4,0),((1,4),0)),
   ((4,0),((2,2),0)),((4,0),((4,1),0)),((4,0),((5,0),0)),((4,0),((5,1),0)),((4,0),((0,3),1)),
   ((4,0),((1,0),1)),((4,1),((0,0),0)),((4,1),((0,5),0)),((4,1),((1,0),0)),((4,1),((1,1),0)),
   ((4,1),((1,2),0)),((4,1),((1,3),0)),((4,1),((1,4),0)),((4,1),((2,0),0)),((4,1),((2,1),0)),
   ((4,1),((2,3),0)),((4,1),((2,4),0)),((4,1),((2,5),0)),((4,1),((3,1),0)),((4,1),((5,0),0)),
   ((4,1),((5,1),0)),((4,1),((0,0),1)),((4,1),((0,2),1)),((4,1),((0,3),1)),((4,1),((1,0),1)),
   ((4,1),((1,1),1)),((4,2),((1,2),0)),((4,2),((1,3),0)),((4,2),((1,4),0)),((4,2),((2,2),0)),
   ((4,2),((4,0),0)),((4,2),((5,0),0)),((4,2),((5,1),0)),((4,2),((0,3),1)),((4,2),((1,0),1)),
   ((4,3),((0,0),0)),((4,3),((0,5),0)),((4,3),((1,2),0)),((4,3),((1,5),0)),((4,3),((2,0),0)),
   ((4,3),((2,1),0)),((4,3),((2,3),0)),((4,3),((2,4),0)),((4,3),((2,5),0)),((4,3),((3,1),0)),
   ((4,3),((4,0),0)),((4,3),((4,1),0)),((4,3),((5,0),0)),((4,3),((5,1),0)),((4,3),((0,0),1)),
   ((4,3),((0,2),1)),((4,3),((0,3),1)),((4,3),((1,0),1)),((4,3),((1,1),1)),((5,0),((2,2),0)),
   ((5,0),((5,0),0)),((5,0),((5,1),0)),((5,1),((2,0),0)),((5,1),((2,1),0)),((5,1),((2,3),0)),
   ((5,1),((2,4),0)),((5,1),((2,5),0)),((5,1),((5,0),0)),((5,1),((5,1),0))]

/-- The `ker ∂₂` basis as a list (for the membership sanity check). -/
def kerBasis : List (BaseGroup → ZMod 2) := [kb0, kb1, kb2, kb3, kb4, kb5]

/-- Each basis vector lies in `ker ∂₂`. -/
theorem kerBasis_mem :
    kerBasis.all (fun v => decide (bbBoundary2Fn baseA baseB v = 0)) = true := by
  native_decide

/-- `recon ζ = Σᵢ ζ(freeCellᵢ) • kbᵢ` (systematic basis: `kbᵢ(freeCellⱼ) = δᵢⱼ`). -/
def recon (z : BaseGroup → ZMod 2) : BaseGroup → ZMod 2 := fun h =>
  z (4,4) * kb0 h + z (4,5) * kb1 h + z (5,2) * kb2 h +
  z (5,3) * kb3 h + z (5,4) * kb4 h + z (5,5) * kb5 h

theorem recon_add (a b : BaseGroup → ZMod 2) : recon (a + b) = recon a + recon b := by
  funext h; simp only [recon, Pi.add_apply]; ring

theorem recon_zero : recon 0 = 0 := by funext h; simp [recon]

/-- The factorization map `C` with `recon + id = C ∘ ∂₂` (matrix form, additive). -/
def cCoef (h : BaseGroup) (p : BaseGroup × Fin 2) : ZMod 2 := if (h, p) ∈ cPairs then 1 else 0
def C (w : BaseGroup × Fin 2 → ZMod 2) : BaseGroup → ZMod 2 :=
  fun h => ∑ p : BaseGroup × Fin 2, cCoef h p * w p

theorem C_add (a b : BaseGroup × Fin 2 → ZMod 2) : C (a + b) = C a + C b := by
  funext h
  simp only [C, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem C_zero : C 0 = 0 := by funext h; simp [C]

theorem bb2_zero_chain : bbBoundary2Fn baseA baseB (0 : BaseGroup → ZMod 2) = 0 := by
  funext p; obtain ⟨g, j⟩ := p
  simp only [bbBoundary2Fn, conv_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  split <;> rfl

/-- The factorization `recon + id = C ∘ ∂₂` holds on the `δ_g` basis. -/
theorem factor_basis : ∀ g : BaseGroup,
    recon (Pi.single g 1) + Pi.single g 1
      = C (bbBoundary2Fn baseA baseB (Pi.single g 1)) := by
  native_decide

/-- **Spanning**: every `ker ∂₂` element equals its reconstruction from free-cell coords.
Proved by lifting the `δ_g` factorization to all chains (`funLift`): `recon ζ + ζ = C(∂₂ζ)`
for all `ζ`, which collapses to `recon ζ = ζ` when `∂₂ ζ = 0`. -/
theorem kerBasis_spans (z : BaseGroup → ZMod 2)
    (hz : bbBoundary2Fn baseA baseB z = 0) : recon z = z := by
  have key : recon z + z = C (bbBoundary2Fn baseA baseB z) :=
    funLift (fun z => recon z + z) (fun z => C (bbBoundary2Fn baseA baseB z))
      (by simp only [recon_zero, add_zero])
      (by simp only [bb2_zero_chain, C_zero])
      (by intro a b; dsimp only; rw [recon_add]; abel)
      (by intro a b; dsimp only; rw [bbBoundary2Fn_add, C_add])
      factor_basis z
  rw [hz, C_zero] at key
  funext h
  have hh := congrFun key h
  have hkey : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact hkey _ _ hh

/-- The 6-parameter combination of basis vectors (the systematic form of `recon`). -/
def kcombo (c0 c1 c2 c3 c4 c5 : ZMod 2) : BaseGroup → ZMod 2 := fun h =>
  c0 * kb0 h + c1 * kb1 h + c2 * kb2 h + c3 * kb3 h + c4 * kb4 h + c5 * kb5 h

theorem recon_eq_kcombo (z : BaseGroup → ZMod 2) :
    recon z = kcombo (z (4,4)) (z (4,5)) (z (5,2)) (z (5,3)) (z (5,4)) (z (5,5)) := rfl

/-- M-VANISH on all 64 combinations: `off₀ = off₂ = 0` (both blocks). -/
theorem offVanish_combo : ∀ c0 c1 c2 c3 c4 c5 : ZMod 2, ∀ s : ZMod 2 × ZMod 2,
    V psi0 s (leftHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 ∧
    V psi0 s (rightHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 ∧
    V psi2 s (leftHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 ∧
    V psi2 s (rightHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 := by
  native_decide

/-- **M-VANISH for all ζ ∈ ker ∂₂** (A4 §9.4 Sharpening 1): the CRT components 0 and 2
of `seamC ζ` vanish on both blocks.  (Spanning reduces `ζ` to one of 64 combos.) -/
theorem off_vanish (z : BaseGroup → ZMod 2) (hz : bbBoundary2Fn baseA baseB z = 0)
    (s : ZMod 2 × ZMod 2) :
    V psi0 s (leftHalf (seamC z)) = 0 ∧ V psi0 s (rightHalf (seamC z)) = 0 ∧
    V psi2 s (leftHalf (seamC z)) = 0 ∧ V psi2 s (rightHalf (seamC z)) = 0 := by
  rw [← kerBasis_spans z hz, recon_eq_kcombo]
  exact offVanish_combo _ _ _ _ _ _ s

/-! ## §2b The coset block decomposition

A Smith-coset element `seamC ζ + ∂₂ f` splits, block by block, into the seam profile
plus the `f`-convolution: the A-block (`j = 0`) is `leftHalf (seamC ζ) + conv baseA f`,
the B-block (`j = 1`) is `rightHalf (seamC ζ) + conv baseB f`.  Composed with the CRT
transform `V` (additive, multiplicative through `conv baseA/baseB`), this exposes the
coset's per-component data `off_j(ζ) ⊕ P̂_j · V_j f` that the §10 slot frame bounds. -/

/-- A-block of a coset element: `leftHalf (seamC ζ + ∂₂ f) = leftHalf (seamC ζ) + A⋆f`. -/
theorem leftHalf_coset (ζ f : BaseGroup → ZMod 2) :
    leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f)
      = leftHalf (seamC ζ) + conv baseA f := rfl

/-- B-block of a coset element: `rightHalf (seamC ζ + ∂₂ f) = rightHalf (seamC ζ) + B⋆f`. -/
theorem rightHalf_coset (ζ f : BaseGroup → ZMod 2) :
    rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f)
      = rightHalf (seamC ζ) + conv baseB f := rfl

end Quantum.Stabilizer.Homological.BB.LightStab

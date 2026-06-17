/-
# Phase 6: reducing `MImBound` to the confined-frame floor (§§0–7)

`MImBound` (`SafeSector.lean`, A4 Part II / Theorem D) was the last assumed `Prop` for an
unconditional `d(gross) = 12`: every base 1-cycle in a nonzero Smith class `[seamC ζ]`
(`ζ ∈ ker ∂₂`) has weight ≥ 12, even though the base `[[72,12,6]]` code has distance only 6.

This module performs the **algebraic reduction**: it rewrites the coset weight
`chainWeight (seamC ζ + ∂₂ f)` into the closed `costFromComps` form that the native-decidable
floor engine consumes.  The discharge is then completed downstream — `MImClassify` (reduction)
→ `MImFloorData` / `MImFloor` (engine + soundness) → `MImMembership` (Γ-membership + the
general per-orbit floor) → `MImTransport` (the y-translation symmetry) → `MImFloorY0..Y12`
(the 13 y-orbit-rep floors) → `MImAssembly` (`mimBound_holds`, and the unconditional distance
theorem).  Reuses the CRT frame (`CRTFrame.lean`) and the layer/Fourier machinery built for
the dangerous sector (`LightStab.lean`).

## Structure (the section numbers track A4 §§9–13)

* **§0 weight join** — `chainWeight w = bwt (leftHalf w) + bwt (rightHalf w)` and its layer-sum
  corollary, bridging the noncomputable `bb72Complex.chainWeight` to the per-block, per-`Z₂²`-
  layer `weight3 (slice …)` decomposition.  (The "join" the route hinges on; structural, since
  `seamC ζ + ∂₂ f` is a base 1-chain and `weight_bridge` already decomposes a block.)
* **§2 `ker ∂₂` basis, spanning, M-VANISH** — the systematic basis `kb0..kb5`, `kerBasis_spans`
  (every `ζ ∈ ker ∂₂` is reconstructed from its six free-cell coordinates via `recon`/`kcombo`),
  and A4 §9.4 Sharpening 1, `off_vanish` (CRT components 0 and 2 of `seamC ζ` vanish).
* **§2b coset block decomposition** — `leftHalf_coset`/`rightHalf_coset`: the coset splits as
  the seam profile plus `A⋆f` / `B⋆f`.
* **§3 coset CRT profile** — `Vcoset_L0..R4`: `Vⱼ(coset) = offⱼ(ζ) ⊕ P̂ⱼ · Vⱼ f` (the
  `f`-dependence, via `V_add` and the engine multipliers `Ahat1`/`Ahat4`/`Bhat2`/`unitHat`).
* **§5 exact per-slot weight** — `weight3_eq_wt5` (the Fourier bijection on `Z₃²`): `weight3`
  is an EXACT function of the five CRT components (`WT5_TABLE`, `native_decide`).
* **§6 closed weight form** — `chainWeight_eq_costFromComps`: `chainWeight` as the `Z₂²`-slot
  sum of the ten CRT components' `wt5OfComps`.
* **§7 coset weight in component form** — `chainWeight_coset_eq`: composes §6 with §3 to write
  the coset weight as `costFromComps` of `shifted (seam offset) multiplier (Vⱼ f)` — the exact
  input the floor engine ranges over.

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
set_option maxRecDepth 40000

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
  decide

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

/-! ## §3 The coset CRT profile: `V_j(coset) = off_j(ζ) ⊕ P̂_j · V_j f`

Composing the block split (§2b) with the additivity (`V_add`) and multiplicativity
(`mult_*`) of the CRT transform, the `j`-th component of a coset element is the seam
offset `off_j(ζ) = V_j(seamC ζ)` plus the engine-multiplied free datum `P̂_j · V_j f`
(`P̂ = Â` on the A-block `j=0`, `B̂` on the B-block `j=1`).  The radical multipliers are
`Â₁=Â₃=Ahat1`, `Â₄=Ahat4`, `B̂₂=B̂₃=B̂₄=Bhat2`; the rest are `unitHat`.  These are the
per-slot inputs the §10 slot frame minimizes over the free datum `t̂_j = V_j f`. -/

variable (ζ f : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2)

theorem Vcoset_L0 : V psi0 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi0 s (leftHalf (seamC ζ))) (rmul unitHat (fun s' => V psi0 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A0]
theorem Vcoset_L1 : V psi1 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi1 s (leftHalf (seamC ζ))) (rmul Ahat1 (fun s' => V psi1 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A1]
theorem Vcoset_L2 : V psi2 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi2 s (leftHalf (seamC ζ))) (rmul unitHat (fun s' => V psi2 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A2]
theorem Vcoset_L3 : V psi3 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi3 s (leftHalf (seamC ζ))) (rmul Ahat1 (fun s' => V psi3 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A3]
theorem Vcoset_L4 : V psi4 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi4 s (leftHalf (seamC ζ))) (rmul Ahat4 (fun s' => V psi4 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A4]
theorem Vcoset_R0 : V psi0 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi0 s (rightHalf (seamC ζ))) (rmul unitHat (fun s' => V psi0 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B0]
theorem Vcoset_R1 : V psi1 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi1 s (rightHalf (seamC ζ))) (rmul unitHat (fun s' => V psi1 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B1]
theorem Vcoset_R2 : V psi2 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi2 s (rightHalf (seamC ζ))) (rmul Bhat2 (fun s' => V psi2 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B2]
theorem Vcoset_R3 : V psi3 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi3 s (rightHalf (seamC ζ))) (rmul Bhat2 (fun s' => V psi3 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B3]
theorem Vcoset_R4 : V psi4 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi4 s (rightHalf (seamC ζ))) (rmul Bhat2 (fun s' => V psi4 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B4]

/-! ## §5 The exact per-slot weight (the Fourier bijection)

The torus-Fourier map `g ↦ (V₀,…,V₄)` is a BIJECTION on the 512 layers (Z₃² is
coprime to char 2), so `weight3` is an EXACT function of the 5 CRT components:
`weight3 (slice b s) = wt5OfComps (V ψⱼ s b)`.  This exact per-slot weight is what the
confined-floor engine (`MImFloor`) minimizes over the coset's free data. -/

/-- The exact weight of a torus layer as a function of its 5 CRT-Fourier components
(`v₀ ∈ {0,1}`; index `v₀ + 2·(v₁ + 4·(v₂ + 4·(v₃ + 4·v₄)))`). -/
def WT5_TABLE : Array Nat :=
  #[0,9,6,3,6,3,6,3,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,2,7,6,3,
    6,3,4,5,6,3,6,3,2,7,4,5,6,3,2,7,6,3,6,3,4,5,4,5,4,5,4,5,6,3,2,7,6,3,4,5,2,7,6,3,6,3,4,5,6,3,
    6,3,2,7,6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,4,5,6,3,2,7,6,3,4,5,2,7,6,3,6,3,6,3,4,5,4,5,4,5,4,5,
    2,7,6,3,6,3,4,5,6,3,2,7,6,3,4,5,6,3,6,3,2,7,4,5,2,7,6,3,6,3,2,7,8,1,4,5,4,5,6,3,4,5,4,5,4,5,
    6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,2,7,4,5,4,5,8,1,4,5,6,3,2,7,
    6,3,6,3,4,5,4,5,4,5,2,7,4,5,8,1,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,4,5,2,7,
    6,3,6,3,4,5,6,3,2,7,6,3,4,5,6,3,2,7,6,3,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,2,7,4,5,8,1,4,5,4,5,
    2,7,6,3,6,3,6,3,4,5,4,5,4,5,2,7,8,1,4,5,4,5,6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,2,7,4,5,4,5,8,1,
    6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,6,3,2,7,6,3,4,5,6,3,6,3,2,7,4,5,2,7,6,3,
    6,3,4,5,6,3,6,3,2,7,6,3,4,5,4,5,4,5,2,7,4,5,4,5,8,1,6,3,4,5,4,5,4,5,4,5,6,3,2,7,6,3,2,7,4,5,
    8,1,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,2,7,6,3,6,3,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,2,7,
    8,1,4,5,4,5]

/-- `weight3` read off the 5 CRT components. -/
def wt5OfComps (v0 v1 v2 v3 v4 : Fin 4) : Nat :=
  WT5_TABLE.getD (v0.val + 2*(v1.val + 4*(v2.val + 4*(v3.val + 4*v4.val)))) 99

/-- **The Fourier bijection**: `weight3` is the exact `wt5OfComps` of the layer's
five torus-Fourier coefficients (`native_decide` over the 512 layers). -/
theorem weight3_eq_wt5 : ∀ g : ZMod 3 × ZMod 3 → ZMod 2,
    weight3 g = wt5OfComps (fhat3 g (0,0)) (fhat3 g (0,1)) (fhat3 g (1,0)) (fhat3 g (1,1))
      (fhat3 g (1,2)) := by
  decide

/-- The exact per-slot weight of a block-slice, in CRT components (`V ψⱼ`). -/
theorem weight3_eq_wt5_slice (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    weight3 (slice b s)
      = wt5OfComps (V psi0 s b) (V psi1 s b) (V psi2 s b) (V psi3 s b) (V psi4 s b) := by
  rw [weight3_eq_wt5 (slice b s), ← fourier_bridge0, ← fourier_bridge1, ← fourier_bridge2,
    ← fourier_bridge3, ← fourier_bridge4]

/-! ## §6 The chain weight as a per-slot `wt5` sum of the ten CRT components

The exact per-slot weight (§5) lifts the layer-sum decomposition (§0) to a closed
form: `chainWeight` of any base 1-chain is the sum, over the four `Z₂²` slots, of
`wt5OfComps` applied to the chain's ten CRT components (five per block).  This is the
form the §10 slot frame minimizes over the coset's free data — composing it with the
`f`-dependence (§3) expresses the coset weight as `costFromComps` of the seam offsets
`⊕ Â/B̂·(Vⱼ f)`, the input to the confined-floor enumeration. -/

/-- The chain weight as a sum over `Z₂²` slots of the two blocks' per-slot `wt5`
of their five CRT components. -/
def costFromComps (vL0 vL1 vL2 vL3 vL4 vR0 vR1 vR2 vR3 vR4 : ZMod 2 × ZMod 2 → Fin 4) : Nat :=
  ∑ s : ZMod 2 × ZMod 2,
    (wt5OfComps (vL0 s) (vL1 s) (vL2 s) (vL3 s) (vL4 s)
     + wt5OfComps (vR0 s) (vR1 s) (vR2 s) (vR3 s) (vR4 s))

/-- **The closed weight form** (§0 ▸ §5): `chainWeight` is `costFromComps` of the chain's
ten CRT components (`V ψⱼ s` on each block).  Structural — `chainWeight_eq_layer_sum`
followed by `weight3_eq_wt5_slice` on each block-slice. -/
theorem chainWeight_eq_costFromComps (c : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight c = costFromComps
      (fun s => V psi0 s (leftHalf c)) (fun s => V psi1 s (leftHalf c))
      (fun s => V psi2 s (leftHalf c)) (fun s => V psi3 s (leftHalf c))
      (fun s => V psi4 s (leftHalf c))
      (fun s => V psi0 s (rightHalf c)) (fun s => V psi1 s (rightHalf c))
      (fun s => V psi2 s (rightHalf c)) (fun s => V psi3 s (rightHalf c))
      (fun s => V psi4 s (rightHalf c)) := by
  rw [chainWeight_eq_layer_sum]
  simp_rw [weight3_eq_wt5_slice]
  simp only [costFromComps, Finset.sum_add_distrib]

/-! ## §7 The coset weight in component form (the `f`-dependence)

Composing the closed weight form (§6) with the coset CRT profile (§3) writes the
safe-sector coset weight `chainWeight (seamC ζ + ∂₂ f)` as `costFromComps` of the ten
coset components `shifted (seam offset) multiplier (Vⱼ f)`: each component is the seam
offset `Vⱼ(seamC ζ)` plus the engine-multiplied free datum `P̂ⱼ · Vⱼ f`, with
`Â = (unitHat, Ahat1, unitHat, Ahat1, Ahat4)` on the A-block and
`B̂ = (unitHat, unitHat, Bhat2, Bhat2, Bhat2)` on the B-block.  The helpers
`seamOffL/R` (the per-orbit offsets) and `compF` (the free datum) are the data the
confined-floor enumeration ranges over. -/

/-- The `ζ`-seam offset of CRT component `ψ` on the A-block (`leftHalf (seamC ζ)`). -/
def seamOffL (ζ : BaseGroup → ZMod 2) (psi : BaseGroup → Fin 4) : Ring :=
  fun s => V psi s (leftHalf (seamC ζ))
/-- The `ζ`-seam offset of CRT component `ψ` on the B-block (`rightHalf (seamC ζ)`). -/
def seamOffR (ζ : BaseGroup → ZMod 2) (psi : BaseGroup → Fin 4) : Ring :=
  fun s => V psi s (rightHalf (seamC ζ))
/-- The `j`-th CRT component of the free datum `f`. -/
def compF (f : BaseGroup → ZMod 2) (psi : BaseGroup → Fin 4) : Ring :=
  fun s => V psi s f
/-- A coset component: seam offset `⊕` engine-multiplied free datum. -/
def shifted (o mult vf : Ring) : Ring := fun s => fadd (o s) (rmul mult vf s)

/-- **The coset weight in component form**: `chainWeight (seamC ζ + ∂₂ f)` is
`costFromComps` of the ten coset components `shifted (seam offset) multiplier (Vⱼ f)`
(§6 ▸ §3).  The substitution is the per-block `Vcoset` profile; `rfl` matches the
`shifted` helpers definitionally. -/
theorem chainWeight_coset_eq (ζ f : BaseGroup → ZMod 2) :
    bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f)
      = costFromComps
        (shifted (seamOffL ζ psi0) unitHat (compF f psi0))
        (shifted (seamOffL ζ psi1) Ahat1 (compF f psi1))
        (shifted (seamOffL ζ psi2) unitHat (compF f psi2))
        (shifted (seamOffL ζ psi3) Ahat1 (compF f psi3))
        (shifted (seamOffL ζ psi4) Ahat4 (compF f psi4))
        (shifted (seamOffR ζ psi0) unitHat (compF f psi0))
        (shifted (seamOffR ζ psi1) unitHat (compF f psi1))
        (shifted (seamOffR ζ psi2) Bhat2 (compF f psi2))
        (shifted (seamOffR ζ psi3) Bhat2 (compF f psi3))
        (shifted (seamOffR ζ psi4) Bhat2 (compF f psi4)) := by
  rw [chainWeight_eq_costFromComps]
  simp_rw [Vcoset_L0, Vcoset_L1, Vcoset_L2, Vcoset_L3, Vcoset_L4,
           Vcoset_R0, Vcoset_R1, Vcoset_R2, Vcoset_R3, Vcoset_R4]
  rfl

end Quantum.Stabilizer.Homological.BB.LightStab

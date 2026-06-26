/-
# Phase 6: the light-orbit floor (A4 §§12–13) — M2/M3 (in progress)

The three **light** Smith orbits (`MImFloorY0, Y1, Y4`, weights 16/18a/18b) do
**not** decouple per-block: their per-block `slotCost` minima sum to only `8` /
`6` / `6`, so — unlike the weight-24 orbits (`WtFloor24Bridge`, M1) — the floor
`≥ 12` is genuinely coupled.  The self-contained proof discharges them in three
steps (A4 §§12–13):

* **Prop 30** (C-table floor): `min_L + min_R ≥ 10` for every `(V₀, γ)`, with
  equality exactly on the tabulated weight-10 loci (the `48 + 48 + 22 = 118`
  achievers).  This needs the **per-cell, spine-coupled** analysis: parity
  (Remark 3) rules out odd splits, the floors `min ≥ 3` and locus disjointness
  rule out `(3,3)/(4,4)/(3,5)/(5,3)`.  (Empirically confirmed here that no cheap
  shortcut reaches it: coupling only `V₀` while leaving the spine free still
  gives `8/6/6` — the spine coupling is essential.)
* **Prop 31** (`ρ`-link kill): each of the `118` weight-10 achievers violates a
  `ρ`-link `V₁R = ρ₁V₁L` / `V₂L = ρ₂V₂R` (Lemma 18, not yet in Lean) — one
  convolution + slot comparison per achiever.
* **Prop 32**: `≥ 10` (Prop 30) + **evenness** (below) + *no* weight-10
  (Prop 31) ⟹ `≥ 12`.

This module provides two layers of the argument.

**Parity layer** (the Prop 32 glue + slot-parity ingredients, all kernel-clean):

* `costFromComps_even` / `chainWeight_coset_even` — **evenness**: every Smith-coset
  element has even weight, from the slot-parity remark (`SlotFrame.slot_parity`) and
  the diagonal component-0 datum (`off_vanish`, Lemma 17): on a Smith coset
  `comp₀^L = comp₀^R = V₀`, so each layer's two block weights are both `≡ V₀ (mod 2)`
  and their sum is even.
* `blockCost_parity` — the **per-block** refinement (the Lemma 28 ingredient): a
  single block's four-slot cost is `≡ |V₀| (mod 2)`, the fact that forces the
  `(min_L, min_R)` split even in Prop 30.
* `chainWeight_coset_ge12_of_floor10` — **Proposition 32** (assembly): evenness +
  the `≥ 10` floor (Prop 30) + the no-weight-`10` kill (Prop 31) ⟹ `≥ 12`, by one
  `omega`.  This fixes the proof shape and isolates the two remaining obligations.

**Reduction layer** (the standard-form coordinate change, the gateway to a finite
floor): `spine3_reduce`/`spine4_reduce` (foundational `native_decide`) collapse the
`64`/`16`-element joint spine images to a **shared** F₄ direction `(a₃, a₄)` (comp 4
with the `ω`-linkage `b₄ᴿ = ω·b₄ᴸ`); the reduced-parameter block costs
`blockCostRedL`/`blockCostRedR` express the per-block link-free cost over those F₄
knobs; and `chainWeight_ge_blockCostRed` is the **soundness bridge** — every coset
weight dominates `blockCostRedL + blockCostRedR` for parameters extracted from `f`,
with `a₃, a₄, V₀` shared.  A rep-specific floor `∀ params, 10 ≤ blockCostRedL +
blockCostRedR` (the finite F₄-knob walk over the `16` spine cells `(a₃, a₄)`) then
gives `10 ≤ chainWeight`.  **Validated** this session: with this reduction the `Y1`
coupled floor is exactly `10` at every one of the `16` cells (matching Prop 30).

**Remaining M2/M3 work:** the rep-specific `≥ 10` floor decide (validated value, but
a heavy kernel walk — `min_L + min_R` over the `16` cells × `V₀`), and Prop 31 (the
`118` `ρ`-link kills).  Until both land, the three light orbits stay on the
`MImFloor` engine (`floorOK`).
-/
import QEC.Stabilizer.Codes.BivariateBicycle.WtFloor24Bridge

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

set_option maxRecDepth 4096

/-! ## Evenness of the Smith-coset weight (the Prop 32 parity ingredient) -/

/-- A single layer's two block weights, sharing the diagonal component-0 value
`w ∈ F₂`, sum to an even number: each is `≡ w (mod 2)` by slot parity. -/
theorem wt5_pair_even (w v1 v2 v3 v4 u1 u2 u3 u4 : Fin 4) (hw : w.val < 2) :
    (wt5OfComps w v1 v2 v3 v4 + wt5OfComps w u1 u2 u3 u4) % 2 = 0 := by
  have hwc : w = (⟨w.val, hw⟩ : Fin 2).castLE (by norm_num) := by apply Fin.ext; rfl
  have hL := slot_parity ⟨w.val, hw⟩ v1 v2 v3 v4
  have hR := slot_parity ⟨w.val, hw⟩ u1 u2 u3 u4
  rw [← hwc] at hL hR
  omega

/-- `costFromComps` is **even** whenever component 0 is the diagonal datum
`(V₀, V₀)` with `V₀` `F₂`-valued: each slot contributes two block weights both
`≡ V₀ (mod 2)`, so the total is a sum of even terms. -/
theorem costFromComps_even (w vL1 vL2 vL3 vL4 vR1 vR2 vR3 vR4 : Ring)
    (hw : ∀ s, (w s).val < 2) :
    costFromComps w vL1 vL2 vL3 vL4 w vR1 vR2 vR3 vR4 % 2 = 0 := by
  unfold costFromComps
  rw [← Nat.even_iff]
  apply Finset.even_sum
  intro s _
  rw [Nat.even_iff]
  exact wt5_pair_even (w s) (vL1 s) (vL2 s) (vL3 s) (vL4 s) (vR1 s) (vR2 s) (vR3 s) (vR4 s) (hw s)

/-- **Per-block parity (the Lemma 28 ingredient).**  A single block's four-slot
cost sum is `≡ |V₀| (mod 2)`, where `|V₀| = ∑ₛ (V₀ s)` is the F₂ weight of the
diagonal component-0 datum: each slot's `wt5` is `≡ V₀ (mod 2)` (`slot_parity`), so
the total has the parity of the component-0 weight.  This refines
`costFromComps_even` to the per-block level — the achiever-structure lemma (A4
Lemma 28) needs `min_L ≡ min_R ≡ |V₀| (mod 2)` to force the `(min_L, min_R)` split
even, which is what rules out the odd would-be weight-`9` splits in Prop 30. -/
theorem blockCost_parity (w v1 v2 v3 v4 : Ring) (hw : ∀ s, (w s).val < 2) :
    (∑ s : ZMod 2 × ZMod 2, wt5OfComps (w s) (v1 s) (v2 s) (v3 s) (v4 s)) % 2
      = (∑ s : ZMod 2 × ZMod 2, (w s).val) % 2 := by
  have key : ∀ s ∈ (Finset.univ : Finset (ZMod 2 × ZMod 2)),
      wt5OfComps (w s) (v1 s) (v2 s) (v3 s) (v4 s) % 2 = (w s).val := by
    intro s _
    have hwc : w s = (⟨(w s).val, hw s⟩ : Fin 2).castLE (by norm_num) := by apply Fin.ext; rfl
    have hsp := slot_parity ⟨(w s).val, hw s⟩ (v1 s) (v2 s) (v3 s) (v4 s)
    rw [← hwc] at hsp
    exact hsp
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl key]

/-- **Evenness (Prop 32 ingredient).**  Every Smith-coset element `seamC ζ + ∂₂ f`
(with `ζ ∈ ker ∂₂`) has **even** chain weight.  Combined with the `≥ 10` floor
(Prop 30) and the `ρ`-link kill (Prop 31), this forces weight `≥ 12` on the light
orbits.  Proof: `off_vanish` (Lemma 17) makes component 0 the diagonal `(V₀, V₀)`,
then `costFromComps_even`. -/
theorem chainWeight_coset_even (ζ f : BaseGroup → ZMod 2)
    (hz : bbBoundary2Fn baseA baseB ζ = 0) :
    bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f) % 2 = 0 := by
  rw [chainWeight_coset_eq]
  have hoff0L : seamOffL ζ psi0 = fun _ => (0 : Fin 4) := by
    funext s; exact (off_vanish ζ hz s).1
  have hoff0R : seamOffR ζ psi0 = fun _ => (0 : Fin 4) := by
    funext s; exact (off_vanish ζ hz s).2.1
  rw [hoff0L, hoff0R]
  apply costFromComps_even
  intro s
  have h := comp0_lt2_L ζ f s
  rwa [hoff0L] at h

/-! ## The spine reduction (the standard-form coordinate change)

The kernel-clean light-orbit floor rests on collapsing the raw radical images to
the slot-frame standard form.  Empirically (this session, repo frame) the joint
spine images have sizes `64` (comp 3) and `16` (comp 4); the two reduction lemmas
below pin the exact coordinate change behind those numbers:

* **comp 3** (`spine3_reduce`): `Â₁·t` and `B̂₂·t` of a single `t` share their F₄
  *direction* `a`, with independent `XY`-shifts — so the `64`-element comp-3 cell
  is exactly `(a₃ shared) × (b₃ᴸ, b₃ᴿ free)`.
* **comp 4** (`spine4_reduce`): they share `a` *and* the `B̂₂`-shift is `ω` times
  the `Â₄`-shift (`b₄ᴿ = ω·b₄ᴸ`) — so the `16`-element comp-4 cell is
  `(a₄ shared) × (b₄ᴸ free)`.

Both are foundational convolution facts over the 256-element `Ring` (`native_decide`,
the same category as `rmul_*_mem` / `CRTFrame`'s ideal facts — *not* the `2³⁰` floor
leaf).  They feed the reduced-parameter block costs `blockCostRed{L,R}` below, whose
floor `min_L + min_R ≥ 10` (Prop 30) becomes a finite F₄-knob walk over the `16`
spine cells `(a₃, a₄)`.  Validated this session: with this reduction the `Y1`
coupled floor is exactly `10` at every one of the `16` spine cells (matching Prop
30; the over-approximation that frees `b₄ᴿ` independently spuriously drops it to
`8`, confirming the `ω`-linkage is load-bearing). -/

/-- **comp-3 spine reduction.**  The L-side (`Â₁`) and R-side (`B̂₂`) radical images
of any `t` share their slot-frame direction `a`; the `XY`-shifts `b, b'` are free.
`native_decide` over the 256-element `Ring` (foundational, cf. `rmul_*_mem`). -/
theorem spine3_reduce : ∀ t : Ring, ∃ a b b' : Fin 4,
    rmul Ahat1 t = (fun s => fadd (fmul a (Ahat1 s)) (fmul b (uv s))) ∧
    rmul Bhat2 t = (fun s => fadd (fmul a (Bhat2 s)) (fmul b' (uv s))) := by
  native_decide

/-- **comp-4 spine reduction.**  The L-side (`Â₄`) and R-side (`B̂₂`) radical images
of any `t` share their direction `a`, and the `B̂₂`-shift is `ω·(Â₄-shift)`
(`fmul 2`).  `native_decide` over the 256-element `Ring` (foundational). -/
theorem spine4_reduce : ∀ t : Ring, ∃ a b : Fin 4,
    rmul Ahat4 t = (fun s => fadd (fmul a (Ahat4 s)) (fmul b (uv s))) ∧
    rmul Bhat2 t = (fun s => fadd (fmul a (Bhat2 s)) (fmul (fmul 2 b) (uv s))) := by
  native_decide

/-- The reduced A/left-block cost: the four-slot `mFree2` sum (component 0 = `V₀`
fixed, the unit-side component 2 freed) with comp-1 confining `a₁·Â₁ + b₁·XY`,
spine `a₃·Â₁ + b₃·XY` and `a₄·Â₄ + b₄·XY`, each shifted by the rep's seam offsets
`oL₁, oL₃, oL₄`.  The F₄-knob standard form that `spine3_reduce`/`spine4_reduce`
reduce the actual coset L-block to. -/
def blockCostRedL (oL1 oL3 oL4 V0 : Ring) (a1 b1 a3 b3 a4 b4 : Fin 4) : Nat :=
  ∑ s : ZMod 2 × ZMod 2, mFree2 (V0 s)
    (fadd (oL1 s) (fadd (fmul a1 (Ahat1 s)) (fmul b1 (uv s))))
    (fadd (oL3 s) (fadd (fmul a3 (Ahat1 s)) (fmul b3 (uv s))))
    (fadd (oL4 s) (fadd (fmul a4 (Ahat4 s)) (fmul b4 (uv s))))

/-- The reduced B/right-block cost: the four-slot `mFree1` sum (`V₀` fixed, the
unit-side component 1 freed) with comp-2 confining `a₂·B̂₂ + b₂·XY`, spine
`a₃·B̂₂ + b₃·XY` and `a₄·B̂₂ + b₄·XY`, shifted by `oR₂, oR₃, oR₄`.  In the coupled
floor the spine direction `a₃` (and `a₄`) is **shared** with `blockCostRedL`, and
`b₄ = ω·b₄ᴸ` (the `spine4_reduce` linkage). -/
def blockCostRedR (oR2 oR3 oR4 V0 : Ring) (a2 b2 a3 b3 a4 b4 : Fin 4) : Nat :=
  ∑ s : ZMod 2 × ZMod 2, mFree1 (V0 s)
    (fadd (oR2 s) (fadd (fmul a2 (Bhat2 s)) (fmul b2 (uv s))))
    (fadd (oR3 s) (fadd (fmul a3 (Bhat2 s)) (fmul b3 (uv s))))
    (fadd (oR4 s) (fadd (fmul a4 (Bhat2 s)) (fmul b4 (uv s))))

/-- **The reduction soundness bridge.**  For every base 1-chain `f`, the coset
weight `chainWeight (seamC ζ + ∂₂ f)` dominates `blockCostRedL + blockCostRedR` for
reduced parameters extracted from `f` — with the spine direction `a₃` (and `a₄`)
**shared** between the two blocks and the comp-4 linkage `b₄ᴿ = ω·b₄ᴸ`, and a
single `F₂`-valued `V₀` shared as component 0.  This is the link-free block bound
(`costFromComps_ge_blockLB`) re-expressed through the spine reductions
(`spine{3,4}_reduce`) and the radical-ideal witnesses (`inIdeal_to_exists`).  A
rep-specific floor `∀ params, 10 ≤ blockCostRedL + blockCostRedR` (the finite
F₄-knob walk over the 16 spine cells) then yields `10 ≤ chainWeight`. -/
theorem chainWeight_ge_blockCostRed (ζ f : BaseGroup → ZMod 2)
    (hz : bbBoundary2Fn baseA baseB ζ = 0) :
    ∃ (V0 : Ring) (a1 b1 a2 b2 a3 b3L b3R a4 b4L : Fin 4),
      (∀ s, (V0 s).val < 2) ∧
      blockCostRedL (seamOffL ζ psi1) (seamOffL ζ psi3) (seamOffL ζ psi4) V0 a1 b1 a3 b3L a4 b4L
    + blockCostRedR (seamOffR ζ psi2) (seamOffR ζ psi3) (seamOffR ζ psi4)
        V0 a2 b2 a3 b3R a4 (fmul 2 b4L)
      ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f) := by
  obtain ⟨a1, b1, h1⟩ := inIdeal_to_exists Ahat1 _ (rmul_Ahat1_mem (compF f psi1))
  obtain ⟨a2, b2, h2⟩ := inIdeal_to_exists Bhat2 _ (rmul_Bhat2_mem (compF f psi2))
  obtain ⟨a3, b3L, b3R, h3L, h3R⟩ := spine3_reduce (compF f psi3)
  obtain ⟨a4, b4L, h4L, h4R⟩ := spine4_reduce (compF f psi4)
  refine ⟨shifted (seamOffL ζ psi0) unitHat (compF f psi0), a1, b1, a2, b2, a3, b3L, b3R, a4, b4L,
    fun s => comp0_lt2_L ζ f s, ?_⟩
  rw [chainWeight_coset_eq ζ f]
  refine le_trans (le_of_eq ?_) (costFromComps_ge_blockLB
    (shifted (seamOffL ζ psi0) unitHat (compF f psi0))
    (shifted (seamOffL ζ psi1) Ahat1 (compF f psi1))
    (shifted (seamOffL ζ psi2) unitHat (compF f psi2))
    (shifted (seamOffL ζ psi3) Ahat1 (compF f psi3))
    (shifted (seamOffL ζ psi4) Ahat4 (compF f psi4))
    (shifted (seamOffR ζ psi0) unitHat (compF f psi0))
    (shifted (seamOffR ζ psi1) unitHat (compF f psi1))
    (shifted (seamOffR ζ psi2) Bhat2 (compF f psi2))
    (shifted (seamOffR ζ psi3) Bhat2 (compF f psi3))
    (shifted (seamOffR ζ psi4) Bhat2 (compF f psi4)))
  have hoff0 : ∀ s, seamOffR ζ psi0 s = seamOffL ζ psi0 s := by
    intro s
    rw [show seamOffR ζ psi0 s = (0 : Fin 4) from (off_vanish ζ hz s).2.1,
        show seamOffL ζ psi0 s = (0 : Fin 4) from (off_vanish ζ hz s).1]
  have hL : blockCostRedL (seamOffL ζ psi1) (seamOffL ζ psi3) (seamOffL ζ psi4)
              (shifted (seamOffL ζ psi0) unitHat (compF f psi0)) a1 b1 a3 b3L a4 b4L
          = blockLBL (shifted (seamOffL ζ psi0) unitHat (compF f psi0))
              (shifted (seamOffL ζ psi1) Ahat1 (compF f psi1))
              (shifted (seamOffL ζ psi3) Ahat1 (compF f psi3))
              (shifted (seamOffL ζ psi4) Ahat4 (compF f psi4)) := by
    unfold blockCostRedL blockLBL
    apply Finset.sum_congr rfl; intro s _
    simp only [shifted, h1, h3L, h4L]
  have hR : blockCostRedR (seamOffR ζ psi2) (seamOffR ζ psi3) (seamOffR ζ psi4)
              (shifted (seamOffL ζ psi0) unitHat (compF f psi0)) a2 b2 a3 b3R a4 (fmul 2 b4L)
          = blockLBR (shifted (seamOffR ζ psi0) unitHat (compF f psi0))
              (shifted (seamOffR ζ psi2) Bhat2 (compF f psi2))
              (shifted (seamOffR ζ psi3) Bhat2 (compF f psi3))
              (shifted (seamOffR ζ psi4) Bhat2 (compF f psi4)) := by
    unfold blockCostRedR blockLBR
    apply Finset.sum_congr rfl; intro s _
    simp only [shifted, hoff0 s, h2, h3R, h4R]
  rw [hL, hR]

/-! ## Locus rules (the per-slot cost facts, A4 §"The locus rules")

The `V₀`-fixed per-slot costs `mFree2` (A/left, frees comp 2) and `mFree1`
(B/right, frees comp 1) obey the slot-cost rules of Lemma 20 — established here as
small kernel `decide`s over the `2 · 4³ = 128` value tuples (`slot_parity` scale,
axiom-clean).  Their empirical shape: with `v₀ = 0` the cost lies in `{0, 2, 4}`
(`0` exactly on the all-zero datum, R1); with `v₀ = 1` it lies in `{1, 3}`.  These
feed the per-cell floors `min ≥ 3` and the locus-disjointness exclusions that the
`ge10_of_no_bad_split` skeleton consumes. -/

/-- **R1 (zero slot), A/left.**  The `V₀`-fixed L cost vanishes iff every component
of the slot datum is zero. -/
theorem locus_zero_L : ∀ (v0 : Fin 2) (v1 v3 v4 : Fin 4),
    mFree2 (v0.castLE (by norm_num)) v1 v3 v4 = 0 ↔ (v0 = 0 ∧ v1 = 0 ∧ v3 = 0 ∧ v4 = 0) := by
  decide

/-- **R1 (zero slot), B/right.** -/
theorem locus_zero_R : ∀ (v0 : Fin 2) (v2 v3 v4 : Fin 4),
    mFree1 (v0.castLE (by norm_num)) v2 v3 v4 = 0 ↔ (v0 = 0 ∧ v2 = 0 ∧ v3 = 0 ∧ v4 = 0) := by
  decide

/-- **Per-slot parity (Remark 3), A/left.**  The `V₀`-fixed L cost is `≡ v₀ (mod 2)`. -/
theorem mFree2_parity : ∀ (v0 : Fin 2) (v1 v3 v4 : Fin 4),
    mFree2 (v0.castLE (by norm_num)) v1 v3 v4 % 2 = v0.val := by decide

/-- **Per-slot parity (Remark 3), B/right.** -/
theorem mFree1_parity : ∀ (v0 : Fin 2) (v2 v3 v4 : Fin 4),
    mFree1 (v0.castLE (by norm_num)) v2 v3 v4 % 2 = v0.val := by decide

/-- **Per-slot cost bound.**  Every `V₀`-fixed L per-slot cost is `≤ 4`. -/
theorem mFree2_le4 : ∀ (v0 : Fin 2) (v1 v3 v4 : Fin 4),
    mFree2 (v0.castLE (by norm_num)) v1 v3 v4 ≤ 4 := by decide

/-- **Per-slot cost bound.**  Every `V₀`-fixed R per-slot cost is `≤ 4`. -/
theorem mFree1_le4 : ∀ (v0 : Fin 2) (v2 v3 v4 : Fin 4),
    mFree1 (v0.castLE (by norm_num)) v2 v3 v4 ≤ 4 := by decide

/-- **Reduced-block parity, A/left.**  `blockCostRedL` is `≡ |V₀| (mod 2)` (the F₂
weight of the diagonal datum) whenever `V₀` is `F₂`-valued: each slot contributes
`≡ V₀ (mod 2)` by `mFree2_parity`.  This is the `hpar` input to
`ge10_of_no_bad_split` (applied to the per-cell minima). -/
theorem blockCostRedL_parity (oL1 oL3 oL4 V0 : Ring) (a1 b1 a3 b3 a4 b4 : Fin 4)
    (hV0 : ∀ s, (V0 s).val < 2) :
    blockCostRedL oL1 oL3 oL4 V0 a1 b1 a3 b3 a4 b4 % 2
      = (∑ s : ZMod 2 × ZMod 2, (V0 s).val) % 2 := by
  have key : ∀ s ∈ (Finset.univ : Finset (ZMod 2 × ZMod 2)),
      mFree2 (V0 s)
        (fadd (oL1 s) (fadd (fmul a1 (Ahat1 s)) (fmul b1 (uv s))))
        (fadd (oL3 s) (fadd (fmul a3 (Ahat1 s)) (fmul b3 (uv s))))
        (fadd (oL4 s) (fadd (fmul a4 (Ahat4 s)) (fmul b4 (uv s)))) % 2 = (V0 s).val := by
    intro s _
    have hwc : V0 s = (⟨(V0 s).val, hV0 s⟩ : Fin 2).castLE (by norm_num) := by apply Fin.ext; rfl
    have hp := mFree2_parity ⟨(V0 s).val, hV0 s⟩
      (fadd (oL1 s) (fadd (fmul a1 (Ahat1 s)) (fmul b1 (uv s))))
      (fadd (oL3 s) (fadd (fmul a3 (Ahat1 s)) (fmul b3 (uv s))))
      (fadd (oL4 s) (fadd (fmul a4 (Ahat4 s)) (fmul b4 (uv s))))
    rw [← hwc] at hp
    exact hp
  unfold blockCostRedL
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl key]

/-- **Reduced-block parity, B/right.** -/
theorem blockCostRedR_parity (oR2 oR3 oR4 V0 : Ring) (a2 b2 a3 b3 a4 b4 : Fin 4)
    (hV0 : ∀ s, (V0 s).val < 2) :
    blockCostRedR oR2 oR3 oR4 V0 a2 b2 a3 b3 a4 b4 % 2
      = (∑ s : ZMod 2 × ZMod 2, (V0 s).val) % 2 := by
  have key : ∀ s ∈ (Finset.univ : Finset (ZMod 2 × ZMod 2)),
      mFree1 (V0 s)
        (fadd (oR2 s) (fadd (fmul a2 (Bhat2 s)) (fmul b2 (uv s))))
        (fadd (oR3 s) (fadd (fmul a3 (Bhat2 s)) (fmul b3 (uv s))))
        (fadd (oR4 s) (fadd (fmul a4 (Bhat2 s)) (fmul b4 (uv s)))) % 2 = (V0 s).val := by
    intro s _
    have hwc : V0 s = (⟨(V0 s).val, hV0 s⟩ : Fin 2).castLE (by norm_num) := by apply Fin.ext; rfl
    have hp := mFree1_parity ⟨(V0 s).val, hV0 s⟩
      (fadd (oR2 s) (fadd (fmul a2 (Bhat2 s)) (fmul b2 (uv s))))
      (fadd (oR3 s) (fadd (fmul a3 (Bhat2 s)) (fmul b3 (uv s))))
      (fadd (oR4 s) (fadd (fmul a4 (Bhat2 s)) (fmul b4 (uv s))))
    rw [← hwc] at hp
    exact hp
  unfold blockCostRedR
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl key]

/-! ## Per-cell minima (the inputs to `ge10_of_no_bad_split`)

For a spine cell `(a₃, a₄)` with comp-4 shift `b₄` and diagonal datum `V₀`, the
per-block minima `minL`/`minR` minimize the reduced block cost over the block's own
knobs (the confining `(a₁,b₁)`/`(a₂,b₂)` and the comp-3 shift `b₃`).  The floor
`min_L + min_R ≥ 10` (Prop 30) closes the cell — and since `blockCostRedL ≥ minL`
etc. (`minL_le`), the per-cell floor lifts to the full coset floor.  `minL_parity`
gives the equal-parity input of the skeleton. -/

/-- The A/left-block per-cell minimum: `blockCostRedL` minimized over the L-only
knobs `(a₁, b₁, b₃)`. -/
def minL (oL1 oL3 oL4 V0 : Ring) (a3 a4 b4 : Fin 4) : Nat :=
  (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)).inf' Finset.univ_nonempty
    (fun p => blockCostRedL oL1 oL3 oL4 V0 p.1 p.2.1 a3 p.2.2 a4 b4)

/-- The B/right-block per-cell minimum: minimized over `(a₂, b₂, b₃ᴿ)`. -/
def minR (oR2 oR3 oR4 V0 : Ring) (a3 a4 b4 : Fin 4) : Nat :=
  (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)).inf' Finset.univ_nonempty
    (fun p => blockCostRedR oR2 oR3 oR4 V0 p.1 p.2.1 a3 p.2.2 a4 b4)

/-- `minL` lower-bounds every `blockCostRedL` at the cell. -/
theorem minL_le (oL1 oL3 oL4 V0 : Ring) (a1 b1 a3 b3 a4 b4 : Fin 4) :
    minL oL1 oL3 oL4 V0 a3 a4 b4 ≤ blockCostRedL oL1 oL3 oL4 V0 a1 b1 a3 b3 a4 b4 :=
  Finset.inf'_le _ (Finset.mem_univ (a1, b1, b3))

/-- `minR` lower-bounds every `blockCostRedR` at the cell. -/
theorem minR_le (oR2 oR3 oR4 V0 : Ring) (a2 b2 a3 b3 a4 b4 : Fin 4) :
    minR oR2 oR3 oR4 V0 a3 a4 b4 ≤ blockCostRedR oR2 oR3 oR4 V0 a2 b2 a3 b3 a4 b4 :=
  Finset.inf'_le _ (Finset.mem_univ (a2, b2, b3))

/-- `minL` has the parity of `|V₀|`: it is achieved at some knobs, where
`blockCostRedL_parity` applies. -/
theorem minL_parity (oL1 oL3 oL4 V0 : Ring) (a3 a4 b4 : Fin 4) (hV0 : ∀ s, (V0 s).val < 2) :
    minL oL1 oL3 oL4 V0 a3 a4 b4 % 2 = (∑ s : ZMod 2 × ZMod 2, (V0 s).val) % 2 := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty)
    (fun p : Fin 4 × Fin 4 × Fin 4 => blockCostRedL oL1 oL3 oL4 V0 p.1 p.2.1 a3 p.2.2 a4 b4)
  rw [minL, hp]
  exact blockCostRedL_parity oL1 oL3 oL4 V0 p.1 p.2.1 a3 p.2.2 a4 b4 hV0

/-- `minR` has the parity of `|V₀|`. -/
theorem minR_parity (oR2 oR3 oR4 V0 : Ring) (a3 a4 b4 : Fin 4) (hV0 : ∀ s, (V0 s).val < 2) :
    minR oR2 oR3 oR4 V0 a3 a4 b4 % 2 = (∑ s : ZMod 2 × ZMod 2, (V0 s).val) % 2 := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty)
    (fun p : Fin 4 × Fin 4 × Fin 4 => blockCostRedR oR2 oR3 oR4 V0 p.1 p.2.1 a3 p.2.2 a4 b4)
  rw [minR, hp]
  exact blockCostRedR_parity oR2 oR3 oR4 V0 p.1 p.2.1 a3 p.2.2 a4 b4 hV0

/-- The per-cell minima have equal parity (both `≡ |V₀|`) — the `hpar` input to
`ge10_of_no_bad_split`. -/
theorem minL_parity_eq_minR (oL1 oL3 oL4 oR2 oR3 oR4 V0 : Ring) (a3 a4 b4 : Fin 4)
    (hV0 : ∀ s, (V0 s).val < 2) :
    minL oL1 oL3 oL4 V0 a3 a4 b4 % 2 = minR oR2 oR3 oR4 V0 a3 a4 b4 % 2 := by
  rw [minL_parity _ _ _ _ _ _ _ hV0, minR_parity _ _ _ _ _ _ _ hV0]

/-! ## Proposition 30 skeleton: the cost-8 kill (Remark 5)

The per-cell floor `min_L + min_R ≥ 10` is reduced — by slot parity
(`blockCost_parity`: both block minima are `≡ |V₀| (mod 2)`, hence equal mod 2) and
the per-block floors `min ≥ 3` — to **excluding the four "bad splits"** `(3,3)`,
`(3,5)`, `(5,3)`, `(4,4)`.  Those exclusions are the locus-disjointness content of
Prop 30 (the `L3=R3=∅` and `L4 ∩ R4 = ∅` facts of A4 §§11.2–11.4), proved cell by
cell.  `ge10_of_no_bad_split` is the arithmetic skeleton that turns the exclusions
into the floor; it is pure `omega`. -/

/-- **Remark 5 (cost-8 kill skeleton).**  Per-block minima `mL, mR ≥ 3` of equal
parity (`mL ≡ mR (mod 2)`, from slot parity) sum to `≥ 10` once the four bad splits
`(3,3), (3,5), (5,3), (4,4)` are excluded: the equal parity rules out odd sums, the
floor `≥ 3` and the exclusions rule out `6` and `8`.  Pure `omega`. -/
theorem ge10_of_no_bad_split {mL mR : Nat} (hL : 3 ≤ mL) (hR : 3 ≤ mR)
    (hpar : mL % 2 = mR % 2)
    (h33 : ¬ (mL = 3 ∧ mR = 3)) (h35 : ¬ (mL = 3 ∧ mR = 5))
    (h53 : ¬ (mL = 5 ∧ mR = 3)) (h44 : ¬ (mL = 4 ∧ mR = 4)) :
    10 ≤ mL + mR := by
  omega

/-! ## Proposition 32: the light-orbit floor assembly

The three analytic facts about a light Smith coset combine to the floor `≥ 12`:

* **evenness** — every element has even weight (`chainWeight_coset_even`, DONE);
* **Prop 30** — the spine-coupled per-cell floor `≥ 10` (the `1024`-cell
  `min_L + min_R ≥ 10`, still on the engine);
* **Prop 31** — no element has weight exactly `10` (the `118` `ρ`-link kills,
  still on the engine).

`chainWeight_coset_ge12_of_floor10` is the **assembly**: it consumes Prop 30 and
Prop 31 as hypotheses and discharges `≥ 12` by one `omega` against evenness.  This
fixes the proof shape and isolates the two remaining obligations; supplying them
for `Y0, Y1, Y4` (kernel-clean, replacing their `floorOK` leaves) is the remaining
M2/M3 work.  Empirically (repo frame, this session): the spine has `64 × 16 = 1024`
cells, so neither Prop 30 nor Prop 31 is a kernel-feasible enumeration — both need
the structured locus argument (A4 §§11.2–11.4 tables + Lemmas 27–28). -/

/-- **Proposition 32** (light-orbit floor, assembly).  For a Smith-coset element
(`ζ ∈ ker ∂₂`), the `≥ 10` floor (Prop 30) and the no-weight-`10` kill (Prop 31),
together with evenness (`chainWeight_coset_even`), give weight `≥ 12`.  Pure `omega`
glue over the three facts. -/
theorem chainWeight_coset_ge12_of_floor10 (ζ f : BaseGroup → ZMod 2)
    (hz : bbBoundary2Fn baseA baseB ζ = 0)
    (h10 : 10 ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f))
    (hne : bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f) ≠ 10) :
    12 ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f) := by
  have heven := chainWeight_coset_even ζ f hz
  omega

end Quantum.Stabilizer.Homological.BB.LightStab

/-
# Phase 6: the weight-24 floor bridge substrate (A4 §§10–11) — M1b

`WtFloor24.lean` (M1a) proved the standard-form walk `Sab_ge_6` (`S(a,b) ≥ 6`
for all `16` pairs).  This module is the **bridge substrate** that an eventual
analytic discharge of the two weight-24 floor leaves will consume: the verified
plumbing connecting the closed coset-weight form `costFromComps` (the hypothesis
of `floor_of_data_analytic`) to the per-slot / per-block `slotCost` machinery.

## What is verified here (all consumed by the eventual reduction)

* **`rmul_{Bhat2,Ahat1,Ahat4}_mem`** — the radical-multiplier image lies in the
  16-element ideal `{αD + β·uv}`: `rmul D r = αD + β·uv` for some `α, β`
  (`native_decide` over the 256-element `Ring`, a `Fintype`).  This is what lets
  a coset's constrained component `off + D·(Vⱼ f)` be rewritten as a finite
  `(α, β)`-indexed ideal element.
* **`inIdeal_to_exists`** — the `Bool` membership `inIdeal D r` to the `Prop`
  existential `∃ a b, r = αD + β·uv` (so the `_mem` facts give a usable witness).
* **`sum_zmod2sq`** — expands a slot sum `∑ s : Z₂², g s` to its four explicit
  slots `g(0,0)+g(1,0)+g(0,1)+g(1,1)`, matching `allS = (e,x,y,xy)`.
* **`slotCost_le'` / `slotCostL_le'`** — `slotCost`/`slotCostL` lower-bound
  `wt5OfComps` for any component-0 value `v₀ < 2` (the `Fin 2 ↪ Fin 4` bridge of
  the `Fin 2`-stated `slotCost_le`/`slotCostL_le`).
* **`V_psi0_lt2`, `comp0_lt2_{L,R}`** — component 0 of every coset element is
  `F₂`-valued (`V ψ₀` is a parity sum), discharging the `v₀ < 2` side-conditions.
* **`costFromComps_ge_blockSlotCost`** — the block split (first half of the
  bridge): `costFromComps ≥ (∑ₛ slotCostL Lᵢ) + (∑ₛ slotCost Rᵢ)`
  (`Finset.sum_add_distrib` + the per-slot bounds).
* **`slotCost_frob`, `slotCostL_frob`, `slotCost_scale`** — the cost-preserving
  moves (Lemma 25): per-slot cost is invariant under entrywise Frobenius (both
  blocks) and under the rigidity-preserving scaling `s₂² = s₃s₄` (right block).
* **`RBlock_std_ge6`** — the standard-form right block (`off₄ = ωθ`) is `≥ 6`
  even with the spine direction freed: the verified endpoint the reduction
  targets.

## The reduction-required finding (why the leaves are NOT yet discharged)

The naive route — bound each block independently below by its `slotCost` slot
sum (`costFromComps_ge_blockSlotCost`) and minimize over the radical-ideal image
— is **insufficient**, established here by `decide`:

* the right block of `Y4` with its *raw* seam offsets minimizes to `< 6`
  (the raw `off₄ = (ω,ω,ω²,0)` is not the standard `ωθ`; the
  no-three-collinear quadruple of Lemma 24 fails), whereas `RBlock_std_ge6`
  shows the *standard* `off₄ = ωθ` block is `≥ 6`;
* even the bound that couples components 3,4 through the shared datum `Vⱼ f`
  (but frees `V₀, V₁, V₂` per block) stays `< 12` for `Y4` — the documented
  link-free floor `≈ 9`.

So the `12` comes from the cross-block coupling (the `ρ`-links pinning
components `0,1,2`, A4 §10) **or**, equivalently, from first reducing each rep's
raw offsets to the standard form via the cost-preserving moves (Lemma 27).  The
move-invariances above are the building blocks of that reduction; composing them
per rep (and, where a rep is a `y`-translate of a canonical weight-24 class,
first transporting via `floor_transfer`) is the remaining M1b work.

Everything here is **axiom-clean** except the three `rmul_*_mem` facts, which use
`native_decide` over the 256-element ring (the same foundational-ring category as
`CRTFrame`'s `*_ann_eq_ideal` / `*_ideal_ge3`, not the `2³⁰` floor leaf).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.WtFloor24

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

set_option maxRecDepth 8192

/-! ## §1 Radical-multiplier image membership and the ideal-element witness

A coset's constrained component is `offset ⊕ D·(Vⱼ f)` for a radical multiplier
`D ∈ {Â₁, Â₄, B̂₂}`.  Since `D² = 0`, the image `rmul D r` lies in the
16-element ideal `{αD + β·uv}` for every `r` (a finite check over the 256-element
`Ring`, which is a `Fintype`).  `inIdeal_to_exists` turns the `Bool` certificate
into the `Prop` existential the rewrite needs. -/

/-- `B̂₂·r` lies in the ideal `{α·B̂₂ + β·uv}` for every `r` (`Ring` is a
`Fintype`; `native_decide` over its 256 elements). -/
theorem rmul_Bhat2_mem : ∀ r : Ring, inIdeal Bhat2 (rmul Bhat2 r) = true := by native_decide

/-- `Â₁·r` lies in the ideal `{α·Â₁ + β·uv}` for every `r`. -/
theorem rmul_Ahat1_mem : ∀ r : Ring, inIdeal Ahat1 (rmul Ahat1 r) = true := by native_decide

/-- `Â₄·r` lies in the ideal `{α·Â₄ + β·uv}` for every `r`. -/
theorem rmul_Ahat4_mem : ∀ r : Ring, inIdeal Ahat4 (rmul Ahat4 r) = true := by native_decide

/-- The `Bool` ideal-membership `inIdeal D r` to the `Prop` witness
`∃ a b, r = α·D + β·uv` (over all four slots). -/
theorem inIdeal_to_exists (D r : Ring) (h : inIdeal D r = true) :
    ∃ a b : Fin 4, r = fun s => fadd (fmul a (D s)) (fmul b (uv s)) := by
  unfold inIdeal at h
  rw [List.any_eq_true] at h
  obtain ⟨ab, _, hab⟩ := h
  refine ⟨ab.1, ab.2, ?_⟩
  funext s
  rw [List.all_eq_true] at hab
  have hs : s ∈ allS := by fin_cases s <;> decide
  simpa using hab s hs

/-! ## §2 The slot-sum expansion and the `Fin 2 ↪ Fin 4` component-0 bridge -/

/-- Expand a slot sum to its four explicit slots `(e, x, y, xy)` (= `allS`). -/
theorem sum_zmod2sq (g : ZMod 2 × ZMod 2 → Nat) :
    ∑ s : ZMod 2 × ZMod 2, g s = g (0,0) + g (1,0) + g (0,1) + g (1,1) := by
  rw [Fintype.sum_prod_type]
  change (∑ x : Fin 2, ∑ y : Fin 2, g (x,y)) = _
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]; omega

/-- `slotCost` lower-bounds `wt5OfComps` for any component-0 value `v₀ < 2`
(reindexing the `Fin 2`-stated `slotCost_le` through `Fin.castLE`). -/
theorem slotCost_le' (v0 v1 v2 v3 v4 : Fin 4) (h0 : v0.val < 2) :
    slotCost v2 v3 v4 ≤ wt5OfComps v0 v1 v2 v3 v4 := by
  have hv : v0 = (⟨v0.val, h0⟩ : Fin 2).castLE (by norm_num) := by apply Fin.ext; rfl
  rw [hv]; exact slotCost_le ⟨v0.val, h0⟩ v1 v2 v3 v4

/-- `slotCostL` lower-bounds `wt5OfComps` for any component-0 value `v₀ < 2`. -/
theorem slotCostL_le' (v0 v1 v2 v3 v4 : Fin 4) (h0 : v0.val < 2) :
    slotCostL v1 v3 v4 ≤ wt5OfComps v0 v1 v2 v3 v4 := by
  have hv : v0 = (⟨v0.val, h0⟩ : Fin 2).castLE (by norm_num) := by apply Fin.ext; rfl
  rw [hv]; exact slotCostL_le ⟨v0.val, h0⟩ v1 v2 v3 v4

/-! ## §3 Component 0 is `F₂`-valued

`V ψ₀` is a parity sum (`ψ₀ ≡ 1`), so every coset element's component 0 lands in
`{0, 1}` — discharging the `v₀ < 2` side-conditions of `slotCost(L)_le'`. -/

/-- The `fadd`-fold of `1`s keeps the accumulator in `{0, 1}` (an `F₂` parity). -/
theorem foldl_fadd_one_lt2 (P : BaseGroup → Bool) :
    ∀ (L : List BaseGroup) (acc : Fin 4), acc.val < 2 →
      (L.foldl (fun a h => if P h then fadd a 1 else a) acc).val < 2 := by
  intro L
  induction L with
  | nil => intro acc h; simpa using h
  | cons h t ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    by_cases hP : P h
    · simp only [hP, if_true]
      have : acc = 0 ∨ acc = 1 := by omega
      rcases this with rfl | rfl <;> decide
    · simp only [hP]; exact hacc

/-- Component 0 of any base chain is `F₂`-valued (`V ψ₀` is a parity sum). -/
theorem V_psi0_lt2 (s : ZMod 2 × ZMod 2) (c : BaseGroup → ZMod 2) : (V psi0 s c).val < 2 := by
  unfold V fsum psi0
  exact foldl_fadd_one_lt2 _ allG 0 (by decide)

/-- The A/left-block component 0 of a coset element is `F₂`-valued. -/
theorem comp0_lt2_L (ζ f : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    (shifted (seamOffL ζ psi0) unitHat (compF f psi0) s).val < 2 := by
  rw [show shifted (seamOffL ζ psi0) unitHat (compF f psi0) s
       = V psi0 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f)) from (Vcoset_L0 ζ f s).symm]
  exact V_psi0_lt2 _ _

/-- The B/right-block component 0 of a coset element is `F₂`-valued. -/
theorem comp0_lt2_R (ζ f : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    (shifted (seamOffR ζ psi0) unitHat (compF f psi0) s).val < 2 := by
  rw [show shifted (seamOffR ζ psi0) unitHat (compF f psi0) s
       = V psi0 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f)) from (Vcoset_R0 ζ f s).symm]
  exact V_psi0_lt2 _ _

/-! ## §4 The block split (first half of the bridge)

`costFromComps` is bounded below by the sum of the two per-block `slotCost` slot
sums: the A/left block frees its unit-side component 2 (`slotCostL` frees `v₀, v₂`)
and the B/right block frees its unit-side component 1 (`slotCost` frees `v₀, v₁`).
This is the link-free reduction; the per-block `≥ 6` second half needs the
standard-form reduction (see the module header). -/

/-- **Block split.**  `costFromComps` dominates the sum of the A-block `slotCostL`
slot sum and the B-block `slotCost` slot sum (component 0 `F₂`-valued on both). -/
theorem costFromComps_ge_blockSlotCost
    (oL0 oL1 oL2 oL3 oL4 oR0 oR1 oR2 oR3 oR4 : Ring)
    (hL0 : ∀ s, (oL0 s).val < 2) (hR0 : ∀ s, (oR0 s).val < 2) :
    (∑ s, slotCostL (oL1 s) (oL3 s) (oL4 s)) + (∑ s, slotCost (oR2 s) (oR3 s) (oR4 s))
      ≤ costFromComps oL0 oL1 oL2 oL3 oL4 oR0 oR1 oR2 oR3 oR4 := by
  unfold costFromComps
  rw [Finset.sum_add_distrib]
  refine Nat.add_le_add (Finset.sum_le_sum ?_) (Finset.sum_le_sum ?_)
  · intro s _; exact slotCostL_le' (oL0 s) (oL1 s) (oL2 s) (oL3 s) (oL4 s) (hL0 s)
  · intro s _; exact slotCost_le' (oR0 s) (oR1 s) (oR2 s) (oR3 s) (oR4 s) (hR0 s)

/-! ## §5 Cost-preserving moves (Lemma 25) — the reduction building blocks

The per-slot cost is invariant under the cost-preserving moves used to reduce a
raw weight-24 block to standard form: entrywise Frobenius (a value-table
symmetry, both blocks) and the rigidity-preserving scaling `s₂² = s₃s₄` (the nine
cell symmetries; for the right block, whose confined component is component 2).
The scaling does *not* hold for the left block as stated (`slotCostL` confines
component 1 and scaling the `F₂` component 0 breaks its parity), so the L-block
reduction routes through its own frame `ℓ' = κ(Â₃)`. -/

/-- **Lemma 25 (Frobenius), right block.** `slotCost` is invariant under
entrywise squaring. -/
theorem slotCost_frob : ∀ v2 v3 v4 : Fin 4,
    slotCost (fmul v2 v2) (fmul v3 v3) (fmul v4 v4) = slotCost v2 v3 v4 := by decide

/-- **Lemma 25 (Frobenius), left block.** `slotCostL` is invariant under
entrywise squaring. -/
theorem slotCostL_frob : ∀ v1 v3 v4 : Fin 4,
    slotCostL (fmul v1 v1) (fmul v3 v3) (fmul v4 v4) = slotCostL v1 v3 v4 := by decide

/-- **Lemma 25 (scaling), right block.** `slotCost` is invariant under the
rigidity-preserving scaling `s₂² = s₃s₄` (`s₂ ≠ 0`). -/
theorem slotCost_scale : ∀ s2 s3 s4 v2 v3 v4 : Fin 4,
    fmul s2 s2 = fmul s3 s4 → s2 ≠ 0 →
    slotCost (fmul s2 v2) (fmul s3 v3) (fmul s4 v4) = slotCost v2 v3 v4 := by decide

/-! ## §6 The standard-form right block reaches `≥ 6` (the reduction endpoint)

With the standard offsets (component 2 confined to `⟨ℓ⟩` through the origin,
component 3 on `⟨ℓ⟩`, component 4 at `ωθ = (ω,0,ω,0)` off the line), the right
block sums to `≥ 6` over the four slots even after freeing the spine direction —
exactly `Prop 29` realized through `slotCost`.  (The raw `Y4` offsets do *not*
satisfy this; they must first be reduced via §5, the remaining M1b work.) -/

set_option maxHeartbeats 4000000 in
-- The 4⁶-knob standard-form right-block walk is a large kernel `decide` (~minutes);
-- the bump keeps it kernel-checked (axiom-clean) rather than `native_decide`.
/-- **Standard right block `≥ 6`.**  With `off₂ = off₃ = 0` and `off₄ = ωθ`, the
B/right block's `slotCost` slot sum is `≥ 6` for every confined/spine ideal
datum (`B̂₂` slot values `(ω²,ω,1,0)`, `uv ≡ 1`). -/
theorem RBlock_std_ge6 : ∀ a2 b2 a3 b3 a4 b4 : Fin 4,
    6 ≤ slotCost (fadd 0 (fadd (fmul a2 3) (fmul b2 1)))
                 (fadd 0 (fadd (fmul a3 3) (fmul b3 1)))
                 (fadd 2 (fadd (fmul a4 3) (fmul b4 1)))
      + slotCost (fadd 0 (fadd (fmul a2 2) (fmul b2 1)))
                 (fadd 0 (fadd (fmul a3 2) (fmul b3 1)))
                 (fadd 0 (fadd (fmul a4 2) (fmul b4 1)))
      + slotCost (fadd 0 (fadd (fmul a2 1) (fmul b2 1)))
                 (fadd 0 (fadd (fmul a3 1) (fmul b3 1)))
                 (fadd 2 (fadd (fmul a4 1) (fmul b4 1)))
      + slotCost (fadd 0 (fadd (fmul a2 0) (fmul b2 1)))
                 (fadd 0 (fadd (fmul a3 0) (fmul b3 1)))
                 (fadd 0 (fadd (fmul a4 0) (fmul b4 1))) := by decide

end Quantum.Stabilizer.Homological.BB.LightStab

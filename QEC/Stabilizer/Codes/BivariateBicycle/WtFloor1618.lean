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

This module currently provides the **parity layer** of the argument (the Prop 32
glue and its slot-parity ingredients), all kernel-clean (std-3, no `native_decide`):

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

Prop 30 and Prop 31 (the per-cell spine-coupled walk and the 118 `ρ`-link kills)
are the remaining M2/M3 work.  Empirically (repo frame): the spine has `64 × 16 =
1024` cells (the joint radical images of `t ↦ (Â₁t, B̂₂t)` and `t ↦ (Â₄t, B̂₂t)`),
so neither is a kernel-feasible enumeration — both need the structured locus
argument (A4 §§11.2–11.4 tables + Lemmas 27–28).  Until then the three light orbits
stay on the `MImFloor` engine (`floorOK`).
-/
import QEC.Stabilizer.Codes.BivariateBicycle.WtFloor24Bridge

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

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

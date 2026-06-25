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

This module currently provides the **evenness** ingredient of Prop 32, which is a
direct consequence of the slot-parity remark (`SlotFrame.slot_parity`) and the
diagonal component-0 datum (`off_vanish`, Lemma 17): on a Smith coset
`comp₀^L = comp₀^R = V₀`, so each layer's two block weights are both `≡ V₀ (mod 2)`
and their sum is even.  Prop 30 and Prop 31 (the per-cell spine-coupled walk and
the 118 `ρ`-link kills) are the remaining M2/M3 work; until then the three light
orbits stay on the `MImFloor` engine (`floorOK`).
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

end Quantum.Stabilizer.Homological.BB.LightStab

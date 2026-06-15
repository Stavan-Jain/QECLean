/-
# Phase 6 — LightStab foundation probe (complete, no sorries).

The light-stabilizer classification (A4 §6.3) is a multi-week interlocked proof
(Floor lemma ← one-block ≥16 ← d₃ dictionary; six per-shape kills; endgame
transfers).  This probe banks the pieces that are *cleanly completable today* and
that the eventual proof builds on:

  L4a  boundary weight is even  (⟹ |∂₂f| ≤ 11 collapses to ≤ 10)
  ENG  the engine→layer Floor input: `rmul Â_j r` is `0` or has ≥ 3 F₄-layers
       (∀ r over the 256-ring) — the direct consumer of the M3 engine lemma
  BRG  the layer-vanishing bridge: if a block is zero on an F₂-layer `s`, then
       every Fourier component `V_j` of that block also vanishes at `s`
       (so #F₂-layers ≥ #nonzero-F₄-layers of any `V_j`)

What this probe does NOT contain (the irreducible research core, see report):
the Floor lemma proper (needs the weight constraint + the unit-only-Fourier
exclusion, NOT a corollary of ENG), the sharp one-block ≥16 bound, and the six
per-shape kills + endgame transfers.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.DangerousSector
import QEC.Stabilizer.Codes.BivariateBicycle.CRTFrame

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame

namespace LightStabProbe

/-! ## L4a — boundary weight is even. -/

/-- Every base boundary `∂₂f` is a 1-cycle (`∂₁∂₂ = 0`), hence has even weight. -/
theorem boundary_weight_even (f : BaseGroup → ZMod 2) :
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card % 2 = 0 :=
  cycle_weight_even (bbBoundary2Fn baseA baseB f) (bbBoundaryFn_comp baseA baseB f)

/-- L4a: a boundary of weight ≤ 11 in fact has weight ≤ 10 (evenness). -/
theorem boundary_weight_le_ten (f : BaseGroup → ZMod 2)
    (h11 : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 11) :
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 10 := by
  have he := boundary_weight_even f
  omega

/-! ## ENG — the engine→layer Floor input.

For each radical multiplier `D`, the product `rmul D r` (= `V_j(D⋆·)` for any
component value `r`) is either `0` or has ≥ 3 nonzero F₄-layers, over the entire
256-element ring.  This is the engine support-shape lemma (M3) in the exact form
the Floor argument consumes: it says a *nonzero* radical-multiplied component
already forces three live layers. -/

theorem Ahat1_rmul_zero_or_ge3 : ∀ r : Ring,
    rmul Ahat1 r = (fun _ => 0) ∨ nLayers (rmul Ahat1 r) ≥ 3 := by native_decide

theorem Ahat4_rmul_zero_or_ge3 : ∀ r : Ring,
    rmul Ahat4 r = (fun _ => 0) ∨ nLayers (rmul Ahat4 r) ≥ 3 := by native_decide

theorem Bhat2_rmul_zero_or_ge3 : ∀ r : Ring,
    rmul Bhat2 r = (fun _ => 0) ∨ nLayers (rmul Bhat2 r) ≥ 3 := by native_decide

/-! ## BRG — the layer-vanishing bridge.

If a block `b` is zero on every cell of F₂-layer `s` (`layer h = s → b h = 0`),
then every component transform `V psi s b = 0`.  Contrapositive: a nonzero
`V psi s b` certifies that layer `s` of `b` is nonzero — so the F₂-layer count of
`b` dominates the nonzero-F₄-layer count of any `V psi · b`. -/

theorem V_layer_vanish (psi : BaseGroup → Fin 4) (s : ZMod 2 × ZMod 2)
    (b : BaseGroup → ZMod 2) (hb : ∀ h : BaseGroup, layer h = s → b h = 0) :
    V psi s b = 0 := by
  unfold V fsum
  have hpred : (fun h => decide (layer h = s) && decide (b h = 1))
      = (fun _ : BaseGroup => false) := by
    funext h
    by_cases hl : layer h = s
    · have : b h = 0 := hb h hl
      simp [hl, this]
    · simp [hl]
  rw [hpred]
  induction allG with
  | nil => rfl
  | cons a t ih => simp only [Bool.false_eq_true, if_false]; exact ih

end LightStabProbe

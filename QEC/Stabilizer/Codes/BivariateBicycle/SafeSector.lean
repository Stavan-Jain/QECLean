/-
# Phase 4: the safe sector — the Smith-coset reduction to (M-im)

The safe-sector bound (`SafeSectorGe12`, A4 Part II) reduced to a single
named hypothesis, `MImBound` ((M-im), A4 §8/Theorem D: every chain in a
seam-coset `C(ζ) + im ∂₂`, `ζ ∈ ker ∂₂`, that is not itself a boundary has
weight ≥ 12).  The reduction — the lab's "safe sector sees exactly the Smith
classes" (`im pr_* ⊆ im Δ`, Entry 16; only this inclusion is load-bearing,
per the Entry-27 review) — is **proven here from the deck homotopy (R)**:

For a safe cycle `v` with `w := p(v)`, (R) gives `v + σv = ∂₂(z)` for the
explicit homotopy 2-chain `z`.  Splitting `z` into its two sheets
`z = lift(ζ₀) + σ·lift(ζ₁)` and reading the two sheet components of
`v + σv = ∂₂ z` (both equal `w`) gives

    w = N(ζ₀) + C(ζ₁)  and  w = C(ζ₀) + N(ζ₁),

where `N/C` are the sheet components of the lifted stabilizer (the seam
decomposition `N(ξ) + C(ξ) = ∂₂ ξ`).  Summing: `∂₂(ζ₀ + ζ₁) = w + w = 0`,
so `ζ := ζ₀ + ζ₁ ∈ ker ∂₂`; substituting back: `w = C(ζ) + ∂₂ ζ₀` — exactly
the Smith-coset form.  Then `|v| ≥ |w| ≥ 12` by (M-im).

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`.
**Repo-left = lab-right.**  Sheet 0 = the `coverSec` image; `C = seamC` is
the lab's `d2c` (seam-crossing part), `N = seamN` the `d2nc`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.DangerousSector

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through the lifted-stabilizer and pushforward bridges unfold
-- deep `Prod`/`ZMod` instance chains (same as `CoverTransfer.lean`).
set_option maxRecDepth 4096

/-! ## Sheet decomposition of cover 2-chains -/

/-- Sheet-0 restriction of a cover 2-chain. -/
def sheetC2_0 (z : GrossGroup → ZMod 2) : BaseGroup → ZMod 2 :=
  fun j => z (coverSec j)

/-- Sheet-1 restriction of a cover 2-chain. -/
def sheetC2_1 (z : GrossGroup → ZMod 2) : BaseGroup → ZMod 2 :=
  fun j => z (coverSec j + deckS)

lemma deckS_add_deckS : deckS + deckS = 0 := by decide

lemma coverPi_add_deckS (g : GrossGroup) : coverPi (g + deckS) = coverPi g :=
  (coverPi_fiber g (g + deckS)).mpr (Or.inr rfl)

/-- Every cover point is the section point of its fiber or its deck
partner. -/
lemma cover_point_dichotomy (g : GrossGroup) :
    g = coverSec (coverPi g) ∨ g = coverSec (coverPi g) + deckS :=
  (coverPi_fiber (coverSec (coverPi g)) g).mp (coverPi_coverSec (coverPi g)).symm

/-- A cover 2-chain is the sum of the lifts of its two sheets. -/
lemma liftC2_decomp (z : GrossGroup → ZMod 2) :
    z = liftC2 (sheetC2_0 z) + deckShift0 (liftC2 (sheetC2_1 z)) := by
  funext g
  rw [Pi.add_apply]
  rcases cover_point_dichotomy g with hg | hg
  · have h1 : liftC2 (sheetC2_0 z) g = z g := by
      change (if g = coverSec (coverPi g) then sheetC2_0 z (coverPi g) else 0)
        = z g
      rw [if_pos hg]
      change z (coverSec (coverPi g)) = z g
      rw [← hg]
    have h2 : deckShift0 (liftC2 (sheetC2_1 z)) g = 0 := by
      change (if g + deckS = coverSec (coverPi (g + deckS)) then
        sheetC2_1 z (coverPi (g + deckS)) else 0) = 0
      rw [if_neg ?_]
      intro hcon
      rw [coverPi_add_deckS, ← hg] at hcon
      apply deckS_ne_zero
      have hcon' : g + deckS = g + 0 := by rw [add_zero]; exact hcon
      exact add_left_cancel hcon'
    rw [h1, h2, add_zero]
  · have h1 : liftC2 (sheetC2_0 z) g = 0 := by
      change (if g = coverSec (coverPi g) then sheetC2_0 z (coverPi g) else 0)
        = 0
      rw [if_neg ?_]
      intro hcon
      have hcontra := hcon.symm.trans hg
      apply deckS_ne_zero
      have hg' : coverSec (coverPi g) + 0 = coverSec (coverPi g) + deckS := by
        rw [add_zero]; exact hcontra
      exact (add_left_cancel hg').symm
    have h2 : deckShift0 (liftC2 (sheetC2_1 z)) g = z g := by
      have hgd : g + deckS = coverSec (coverPi g) := by
        rw [hg, add_assoc, deckS_add_deckS, add_zero, coverPi_add_deckS,
          coverPi_coverSec]
      change (if g + deckS = coverSec (coverPi (g + deckS)) then
        sheetC2_1 z (coverPi (g + deckS)) else 0) = z g
      rw [coverPi_add_deckS, if_pos hgd]
      change z (coverSec (coverPi g) + deckS) = z g
      rw [← hg]
    rw [h1, h2, zero_add]

lemma liftC2_add (ξ η : BaseGroup → ZMod 2) :
    liftC2 (ξ + η) = liftC2 ξ + liftC2 η := by
  funext g
  change (if g = coverSec (coverPi g) then (ξ + η) (coverPi g) else 0)
    = (if g = coverSec (coverPi g) then ξ (coverPi g) else 0)
      + (if g = coverSec (coverPi g) then η (coverPi g) else 0)
  by_cases hg : g = coverSec (coverPi g)
  · rw [if_pos hg, if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg, if_neg hg, add_zero]

/-! ## The seam decomposition `∂₂ = N + C` -/

/-- The non-crossing seam part: sheet-0 component of the lifted stabilizer
(the lab's `d2nc`). -/
def seamN (ξ : BaseGroup → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  sheet0 (liftStab ξ)

/-- The seam-crossing part: sheet-1 component of the lifted stabilizer
(the lab's `d2c`).  The Smith connecting map at chain level is
`ζ ↦ seamC ζ` on 2-cycles. -/
def seamC (ξ : BaseGroup → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  sheet1 (liftStab ξ)

/-- The seam split sums to the base boundary. -/
lemma seamN_add_seamC (ξ : BaseGroup → ZMod 2) (j : BaseGroup × Fin 2) :
    seamN ξ j + seamC ξ j = bbBoundary2Fn baseA baseB ξ j := by
  have h := sheet0_add_sheet1 (liftStab ξ) j
  rw [coverPush1_liftStab] at h
  exact h

lemma seamC_add (ξ η : BaseGroup → ZMod 2) :
    seamC (ξ + η) = seamC ξ + seamC η := by
  unfold seamC liftStab
  rw [liftC2_add, bbBoundary2Fn_add, sheet1_add]

/-! ## Deck-shift bookkeeping -/

lemma liftStab_deckShift (ξ : BaseGroup → ZMod 2) :
    bbBoundary2Fn grossA grossB (deckShift0 (liftC2 ξ))
      = deckShift1 (liftStab ξ) :=
  bbBoundary2Fn_translate grossA grossB deckS (liftC2 ξ)

lemma sheet0_deckShift1 (s : GrossGroup × Fin 2 → ZMod 2) :
    sheet0 (deckShift1 s) = sheet1 s := rfl

lemma sheet1_deckShift1 (s : GrossGroup × Fin 2 → ZMod 2) :
    sheet1 (deckShift1 s) = sheet0 s := by
  funext q
  change s ((coverSec1 q).1 + deckS + deckS, (coverSec1 q).2) = s (coverSec1 q)
  rw [add_assoc, deckS_add_deckS, add_zero]

/-- Sheet 0 of `v + σv` is the pushforward. -/
lemma sheet0_self_add_deck (v : GrossGroup × Fin 2 → ZMod 2)
    (j : BaseGroup × Fin 2) :
    sheet0 (v + deckShift1 v) j = coverPush1 v j := by
  rw [sheet0_add, Pi.add_apply, sheet0_deckShift1]
  exact sheet0_add_sheet1 v j

/-- Sheet 1 of `v + σv` is also the pushforward. -/
lemma sheet1_self_add_deck (v : GrossGroup × Fin 2 → ZMod 2)
    (j : BaseGroup × Fin 2) :
    sheet1 (v + deckShift1 v) j = coverPush1 v j := by
  rw [sheet1_add, Pi.add_apply, sheet1_deckShift1, add_comm]
  exact sheet0_add_sheet1 v j

/-! ## The (M-im) hypothesis and the reduction -/

/-- **(M-im)** (A4 Part II / Theorem D): every chain in a Smith seam-coset
`seamC ζ + im ∂₂` (`ζ ∈ ker ∂₂`) that is not itself a base boundary has
weight ≥ 12.  This is the single remaining analytic input for the safe
sector; its paper proof is the confined-floor program of A4 §§9–13. -/
def MImBound : Prop :=
  ∀ ζ : BaseGroup → ZMod 2, bbBoundary2Fn baseA baseB ζ = 0 →
    ∀ f : BaseGroup → ZMod 2,
      seamC ζ + bbBoundary2Fn baseA baseB f ∉ bb72Complex.boundaries →
      12 ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f)

/-- **The safe-sector reduction**: (M-im) implies `SafeSectorGe12`.  The
Smith-coset membership of `p(v)` is derived from the deck homotopy (R). -/
theorem safe_sector_of_mim (hMim : MImBound) : SafeSectorGe12 := by
  intro v hv hb
  -- (R): v + σv = ∂₂(homotopyChain v)
  have hR : bbBoundary2Fn grossA grossB (homotopyChain v) = v + deckShift1 v :=
    bbBoundary2Fn_homotopyChain hv
  -- split the homotopy 2-chain into sheets
  have hsplit : v + deckShift1 v
      = liftStab (sheetC2_0 (homotopyChain v))
        + deckShift1 (liftStab (sheetC2_1 (homotopyChain v))) := by
    rw [← hR]
    conv_lhs => rw [liftC2_decomp (homotopyChain v)]
    rw [bbBoundary2Fn_add, liftStab_deckShift]
    rfl
  -- read the two sheet components: both equal w := p(v)
  have hw0 : ∀ j, coverPush1 v j
      = seamN (sheetC2_0 (homotopyChain v)) j
        + seamC (sheetC2_1 (homotopyChain v)) j := by
    intro j
    calc coverPush1 v j
        = sheet0 (v + deckShift1 v) j := (sheet0_self_add_deck v j).symm
      _ = sheet0 (liftStab (sheetC2_0 (homotopyChain v))
            + deckShift1 (liftStab (sheetC2_1 (homotopyChain v)))) j := by
          rw [hsplit]
      _ = seamN (sheetC2_0 (homotopyChain v)) j
            + seamC (sheetC2_1 (homotopyChain v)) j := by
          rw [sheet0_add, Pi.add_apply, sheet0_deckShift1]
          rfl
  have hw1 : ∀ j, coverPush1 v j
      = seamC (sheetC2_0 (homotopyChain v)) j
        + seamN (sheetC2_1 (homotopyChain v)) j := by
    intro j
    calc coverPush1 v j
        = sheet1 (v + deckShift1 v) j := (sheet1_self_add_deck v j).symm
      _ = sheet1 (liftStab (sheetC2_0 (homotopyChain v))
            + deckShift1 (liftStab (sheetC2_1 (homotopyChain v)))) j := by
          rw [hsplit]
      _ = seamC (sheetC2_0 (homotopyChain v)) j
            + seamN (sheetC2_1 (homotopyChain v)) j := by
          rw [sheet1_add, Pi.add_apply, sheet1_deckShift1]
          rfl
  -- the sheet sum is a 2-cycle
  have hker : bbBoundary2Fn baseA baseB
      (sheetC2_0 (homotopyChain v) + sheetC2_1 (homotopyChain v)) = 0 := by
    funext j
    rw [bbBoundary2Fn_add, Pi.add_apply, Pi.zero_apply]
    have hkey : ∀ n0 c0 n1 c1 w b0 b1 : ZMod 2,
        w = n0 + c1 → w = c0 + n1 → n0 + c0 = b0 → n1 + c1 = b1 →
        b0 + b1 = 0 := by decide
    exact hkey _ _ _ _ _ _ _ (hw0 j) (hw1 j)
      (seamN_add_seamC (sheetC2_0 (homotopyChain v)) j)
      (seamN_add_seamC (sheetC2_1 (homotopyChain v)) j)
  -- the Smith-coset form of w
  have hwform : coverPush1 v
      = seamC (sheetC2_0 (homotopyChain v) + sheetC2_1 (homotopyChain v))
        + bbBoundary2Fn baseA baseB (sheetC2_0 (homotopyChain v)) := by
    funext j
    rw [Pi.add_apply, seamC_add, Pi.add_apply]
    have hkey : ∀ n0 c0 c1 w b0 : ZMod 2,
        w = n0 + c1 → n0 + c0 = b0 → w = (c0 + c1) + b0 := by decide
    exact hkey _ _ _ _ _ (hw0 j)
      (seamN_add_seamC (sheetC2_0 (homotopyChain v)) j)
  -- conclude via (M-im)
  have h12 : 12 ≤ bb72Complex.chainWeight (coverPush1 v) := by
    rw [hwform]
    refine hMim _ hker _ ?_
    rw [← hwform]
    exact hb
  exact le_trans h12 (chainWeight_coverPush_le v)

/-! ## The final conditional assembly

`d(gross) = 12` from exactly the two CRT-engine inputs. -/

/-- **Conditional Pauli-level `d(gross) = 12` on the two CRT-engine
inputs**: the light-stabilizer classification (A4 §6.3) and (M-im)
(A4 Part II).  Everything else — Theorems A and B, the slice machinery, the
m-rungs, (R), the duality, the sector assembly, and the weight-12 witness —
is unconditionally proven in this development. -/
theorem gross_pauli_distance_eq_12_of_engine
    (hC : LightStabilizerClassification) (hMim : MImBound) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  gross_pauli_distance_eq_12_of_two_sectors
    (dangerous_sector_of_classification hC) (safe_sector_of_mim hMim)

/-- Chain-level version of the final conditional assembly. -/
theorem gross_chain_distance_eq_12_of_engine
    (hC : LightStabilizerClassification) (hMim : MImBound) :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 :=
  gross_chain_distance_eq_12_of_sectors base_distance_ge_6
    (dangerous_sector_of_classification hC) (safe_sector_of_mim hMim)

end BB
end Homological
end Stabilizer
end Quantum

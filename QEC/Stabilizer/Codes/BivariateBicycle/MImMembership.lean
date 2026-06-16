/-
# Phase 6: Γ-membership — the engine indices realize the coset's free datum

The chain-weight bridge (`MImFloor §13`) reduces each safe-sector coset weight to
`exCost oL oR a0 a3 a4 k1 k2`, where the five fiber indices `(a0,a3,a4,k1,k2)` must point at
the Γⱼ entries equal to the engine-multiplied free datum `rmul P̂ⱼ (Vⱼ f)`.  This module
supplies those indices and proves they are correct, for *every* free datum `vf : Ring`.

`gammaIdxⱼ vf` searches Γⱼ for the slot-vector of `(rmul B̂ⱼ vf, rmul Âⱼ vf)` (side 0 =
`B̂ⱼ` = repo `rightHalf`; side 1 = `Âⱼ` = `leftHalf`, the convention verified vs `seamC`
in `MImFloor §13`).  The membership theorems (`mem0`..`mem4`, `native_decide` over the
256-element ring) certify the index is in range and the Γ entry matches on both sides.

* `B̂ = (unitHat, unitHat, Bhat2, Bhat2, Bhat2)` on the side-0 (`rightHalf`) block;
* `Â = (unitHat, Ahat1, unitHat, Ahat1, Ahat4)` on the side-1 (`leftHalf`) block.

Comp 0 is the trivial character (`psi0 ≡ 1`), so `compF f psi0 = V psi0 · f` is `F₂`-valued
(`V_psi0_lt2`); its membership is over that restricted image (Γ₀ has 16, not 256, entries).
-/
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloor

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

set_option maxRecDepth 4096

/-! ## §14a The trivial-character component is `F₂`-valued -/

/-- `fadd · 1` keeps the value in `{0,1}` (char-2: `0↦1, 1↦0`). -/
theorem fadd_one_lt2 : ∀ acc : Fin 4, acc.val < 2 → (fadd acc 1).val < 2 := by decide

/-- The trivial character's CRT component is `F₂`-valued: `V psi0 s f ∈ {0,1}` (its `fsum`
folds `fadd · 1`, which preserves `{0,1}`). -/
theorem V_psi0_lt2 (s : ZMod 2 × ZMod 2) (f : BaseGroup → ZMod 2) : (V psi0 s f).val < 2 := by
  unfold V fsum
  have key : ∀ (L : List BaseGroup) (acc : Fin 4), acc.val < 2 →
      (L.foldl (fun acc h =>
        if (decide (layer h = s) && decide (f h = 1)) then fadd acc (psi0 h) else acc)
        acc).val < 2 := by
    intro L
    induction L with
    | nil => exact fun acc h => h
    | cons h t ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      by_cases hp : (decide (layer h = s) && decide (f h = 1)) = true
      · rw [if_pos hp]; exact fadd_one_lt2 acc hacc
      · rw [if_neg hp]; exact hacc
  exact key allG 0 (by decide)

/-! ## §14b The Γ-membership index and its correctness -/

/-- Γ-array index of the slot-value-vector of `(rmul m0 vf, rmul m1 vf)` (side 0 = `m0`,
side 1 = `m1`).  Linear search over the `n` pairs; `999` if absent (never, for valid data). -/
def gammaIdx (G : Array Nat) (n : Nat) (m0 m1 vf : Ring) : Nat :=
  ((List.range n).find? (fun a => decide (∀ s : ZMod 2 × ZMod 2,
    pv G a (natslot s) 0 = (rmul m0 vf s).val ∧
    pv G a (natslot s) 1 = (rmul m1 vf s).val))).getD 999

/-- `|Γ₁| = |Γ₂| = 256` (the full ring; the fiber arrays store all 256 pairs). -/
def nF1 : Nat := F1gen.size / 8
def nF2 : Nat := F2gen.size / 8

/-- Per-component Γ-index of the free datum `vf` (multipliers `B̂ⱼ` side 0, `Âⱼ` side 1). -/
def gammaIdx0 (vf : Ring) : Nat := gammaIdx G0gen nG0 unitHat unitHat vf
def gammaIdx1 (vf : Ring) : Nat := gammaIdx F1gen nF1 unitHat Ahat1 vf
def gammaIdx2 (vf : Ring) : Nat := gammaIdx F2gen nF2 Bhat2 unitHat vf
def gammaIdx3 (vf : Ring) : Nat := gammaIdx G3gen nG3 Bhat2 Ahat1 vf
def gammaIdx4 (vf : Ring) : Nat := gammaIdx G4gen nG4 Bhat2 Ahat4 vf

/-- **Comp-0 membership** (over the `F₂`-valued image; `B̂₀ = Â₀ = unitHat`). -/
theorem mem0 : ∀ vf : Ring, (∀ s : ZMod 2 × ZMod 2, (vf s).val < 2) →
    gammaIdx0 vf < nG0 ∧
    (∀ s, pv G0gen (gammaIdx0 vf) (natslot s) 0 = (rmul unitHat vf s).val) ∧
    (∀ s, pv G0gen (gammaIdx0 vf) (natslot s) 1 = (rmul unitHat vf s).val) := by
  native_decide

/-- **Comp-1 membership** (`B̂₁ = unitHat`, `Â₁ = Ahat1`). -/
theorem mem1 : ∀ vf : Ring,
    gammaIdx1 vf < nF1 ∧
    (∀ s, pv F1gen (gammaIdx1 vf) (natslot s) 0 = (rmul unitHat vf s).val) ∧
    (∀ s, pv F1gen (gammaIdx1 vf) (natslot s) 1 = (rmul Ahat1 vf s).val) := by
  native_decide

/-- **Comp-2 membership** (`B̂₂ = Bhat2`, `Â₂ = unitHat`). -/
theorem mem2 : ∀ vf : Ring,
    gammaIdx2 vf < nF2 ∧
    (∀ s, pv F2gen (gammaIdx2 vf) (natslot s) 0 = (rmul Bhat2 vf s).val) ∧
    (∀ s, pv F2gen (gammaIdx2 vf) (natslot s) 1 = (rmul unitHat vf s).val) := by
  native_decide

/-- **Comp-3 membership** (`B̂₃ = Bhat2`, `Â₃ = Ahat1`). -/
theorem mem3 : ∀ vf : Ring,
    gammaIdx3 vf < nG3 ∧
    (∀ s, pv G3gen (gammaIdx3 vf) (natslot s) 0 = (rmul Bhat2 vf s).val) ∧
    (∀ s, pv G3gen (gammaIdx3 vf) (natslot s) 1 = (rmul Ahat1 vf s).val) := by
  native_decide

/-- **Comp-4 membership** (`B̂₄ = Bhat2`, `Â₄ = Ahat4`). -/
theorem mem4 : ∀ vf : Ring,
    gammaIdx4 vf < nG4 ∧
    (∀ s, pv G4gen (gammaIdx4 vf) (natslot s) 0 = (rmul Bhat2 vf s).val) ∧
    (∀ s, pv G4gen (gammaIdx4 vf) (natslot s) 1 = (rmul Ahat4 vf s).val) := by
  native_decide

end Quantum.Stabilizer.Homological.BB.LightStab

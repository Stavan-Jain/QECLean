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

set_option maxRecDepth 40000

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

/-- The fiber-count abbreviations agree with the flat totals `F*off.getD nC* 0`. -/
theorem nF1_eq : nF1 = F1off.getD nC1 0 := by decide
theorem nF2_eq : nF2 = F2off.getD nC2 0 := by decide

/-! ## §14c The general per-orbit safe-sector floor

Assembles the whole chain for an orbit representative `zrep` with offset arrays `oL, oR`:
chainWeight (§7) → `costFromComps` → (bridge §13) `exCost` → (soundness §12b) `≥ 12`.
The bridge's ten val-equalities are discharged cell-by-cell (`shifted_val_eq`) from the
per-orbit offData (`oLoff*`/`oRoff*`) and the universal Γ-membership (`mem0`..`mem4`); the
comp-1,2 indices land in range via `mem1/mem2 + nF*_eq`.  The per-orbit modules
`MImFloorO0`..`MImFloorO4` instantiate this with their data + `floorOK … = true`. -/

/-- Per-cell discharge of a bridge val-equality: `shifted o mult vf` matches the engine cell
`gadd offset Γ-pair` given the offData (`hoff`) and membership (`hmem`) equalities. -/
theorem shifted_val_eq {o mult vf : Ring} {oarr Garr : Array Nat} {j a side : Nat}
    (s : ZMod 2 × ZMod 2)
    (hoff : (o s).val = ov oarr j (natslot s))
    (hmem : (rmul mult vf s).val = pv Garr a (natslot s) side) :
    (shifted o mult vf s).val = gadd (ov oarr j (natslot s)) (pv Garr a (natslot s) side) := by
  show (fadd (o s) (rmul mult vf s)).val = _
  rw [← gadd_eq_fadd, hoff, hmem]

/-- **The per-orbit safe-sector floor**: every base 1-cycle in the Smith class `[seamC zrep]`
has weight `≥ 12`, given the floor decision `floorOK oL oR = true`, the offset bounds, and the
per-orbit offData (`oL = rightHalf`, `oR = leftHalf`). -/
theorem floor_of_data (zrep : BaseGroup → ZMod 2) (oL oR : Array Nat)
    (hfloor : floorOK oL oR = true)
    (hoL4 : ∀ i, oL.getD i 0 < 4) (hoR4 : ∀ i, oR.getD i 0 < 4)
    (hoL0 : ∀ s, s < 4 → ov oL 0 s < 2) (hoR0 : ∀ s, s < 4 → ov oR 0 s < 2)
    (oLoff0 : ∀ s, (seamOffR zrep psi0 s).val = ov oL 0 (natslot s))
    (oLoff1 : ∀ s, (seamOffR zrep psi1 s).val = ov oL 1 (natslot s))
    (oLoff2 : ∀ s, (seamOffR zrep psi2 s).val = ov oL 2 (natslot s))
    (oLoff3 : ∀ s, (seamOffR zrep psi3 s).val = ov oL 3 (natslot s))
    (oLoff4 : ∀ s, (seamOffR zrep psi4 s).val = ov oL 4 (natslot s))
    (oRoff0 : ∀ s, (seamOffL zrep psi0 s).val = ov oR 0 (natslot s))
    (oRoff1 : ∀ s, (seamOffL zrep psi1 s).val = ov oR 1 (natslot s))
    (oRoff2 : ∀ s, (seamOffL zrep psi2 s).val = ov oR 2 (natslot s))
    (oRoff3 : ∀ s, (seamOffL zrep psi3 s).val = ov oR 3 (natslot s))
    (oRoff4 : ∀ s, (seamOffL zrep psi4 s).val = ov oR 4 (natslot s))
    (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight (seamC zrep + bbBoundary2Fn baseA baseB f) := by
  have hF2 : ∀ s, (compF f psi0 s).val < 2 := fun s => V_psi0_lt2 s f
  have hbridge := costFromComps_eq_exCost oL oR
    (gammaIdx0 (compF f psi0)) (gammaIdx3 (compF f psi3)) (gammaIdx4 (compF f psi4))
    (gammaIdx1 (compF f psi1)) (gammaIdx2 (compF f psi2))
    (shifted (seamOffL zrep psi0) unitHat (compF f psi0))
    (shifted (seamOffL zrep psi1) Ahat1 (compF f psi1))
    (shifted (seamOffL zrep psi2) unitHat (compF f psi2))
    (shifted (seamOffL zrep psi3) Ahat1 (compF f psi3))
    (shifted (seamOffL zrep psi4) Ahat4 (compF f psi4))
    (shifted (seamOffR zrep psi0) unitHat (compF f psi0))
    (shifted (seamOffR zrep psi1) unitHat (compF f psi1))
    (shifted (seamOffR zrep psi2) Bhat2 (compF f psi2))
    (shifted (seamOffR zrep psi3) Bhat2 (compF f psi3))
    (shifted (seamOffR zrep psi4) Bhat2 (compF f psi4))
    (fun s => shifted_val_eq s (oRoff0 s) (((mem0 (compF f psi0) hF2).2.2) s).symm)
    (fun s => shifted_val_eq s (oRoff1 s) (((mem1 (compF f psi1)).2.2) s).symm)
    (fun s => shifted_val_eq s (oRoff2 s) (((mem2 (compF f psi2)).2.2) s).symm)
    (fun s => shifted_val_eq s (oRoff3 s) (((mem3 (compF f psi3)).2.2) s).symm)
    (fun s => shifted_val_eq s (oRoff4 s) (((mem4 (compF f psi4)).2.2) s).symm)
    (fun s => shifted_val_eq s (oLoff0 s) (((mem0 (compF f psi0) hF2).2.1) s).symm)
    (fun s => shifted_val_eq s (oLoff1 s) (((mem1 (compF f psi1)).2.1) s).symm)
    (fun s => shifted_val_eq s (oLoff2 s) (((mem2 (compF f psi2)).2.1) s).symm)
    (fun s => shifted_val_eq s (oLoff3 s) (((mem3 (compF f psi3)).2.1) s).symm)
    (fun s => shifted_val_eq s (oLoff4 s) (((mem4 (compF f psi4)).2.1) s).symm)
  rw [chainWeight_coset_eq zrep f, hbridge]
  exact floorOK_sound_flat oL oR hfloor hoL4 hoR4 hoL0 hoR0
    (mem0 (compF f psi0) hF2).1 (mem3 (compF f psi3)).1 (mem4 (compF f psi4)).1
    (nF1_eq ▸ (mem1 (compF f psi1)).1) (nF2_eq ▸ (mem2 (compF f psi2)).1)

end Quantum.Stabilizer.Homological.BB.LightStab

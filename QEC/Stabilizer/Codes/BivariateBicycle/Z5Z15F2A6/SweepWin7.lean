/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SweepWin4
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SweepWin5
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SweepWin6

/-!
# Z5Z15F2A6 window sweep leaves (7 of 7 — assembly)

Survivor certificates and the public extension-sweep theorems.

`survivorB`/`pairSurvivorB` pass for only finitely many extra cells per
t ≥ 2 class; one cheap `native_decide` certifies each survivor list, and
the public `win_sweepE_*`/`win_sweepP_*` theorems (the exact hypothesis
shapes of `window_sound_t2/t3`) dispatch through `mem_of_filter_eq` to
the per-survivor flat sweeps of `SweepWin4`–`SweepWin6`.  This keeps the
gate quantifiers out of the `native_decide` cores entirely — no inner
ball is ever evaluated behind a `Decidable` arrow instance.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

private theorem win_surv_0 :
    (List.range 150).filter (fun c =>
      !(winMem (0 : Fin 113) (coordOfC1 c)) && survivorB (0 : Fin 113) c)
      = [72, 113] := by
  native_decide

private theorem win_pairs_0 :
    (List.range 22500).filter (fun n =>
      !(n / 150 == n % 150) &&
      (!(winMem (0 : Fin 113) (coordOfC1 (n / 150))) &&
        (!(winMem (0 : Fin 113) (coordOfC1 (n % 150))) &&
          pairSurvivorB (0 : Fin 113) (n / 150) (n % 150))))
      = [1731, 10913, 12161, 12685, 12834, 17022] := by
  native_decide

private theorem win_surv_1 :
    (List.range 150).filter (fun c =>
      !(winMem (1 : Fin 113) (coordOfC1 c)) && survivorB (1 : Fin 113) c)
      = [71, 73, 112, 140, 142] := by
  native_decide

private theorem win_surv_27 :
    (List.range 150).filter (fun c =>
      !(winMem (27 : Fin 113) (coordOfC1 c)) && survivorB (27 : Fin 113) c)
      = [58, 99] := by
  native_decide

private theorem win_surv_28 :
    (List.range 150).filter (fun c =>
      !(winMem (28 : Fin 113) (coordOfC1 c)) && survivorB (28 : Fin 113) c)
      = [47, 57, 98] := by
  native_decide

theorem win_sweepE_0 :
    ∀ e : G150 × Fin 2, winMem (0 : Fin 113) e = false →
      survivorB (0 : Fin 113) (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113) ++ [cellIdx e]).length),
        syndFold (winCellList (0 : Fin 113) ++ [cellIdx e]) lam.val = 0 →
        (tableEntries (0 : Fin 113) (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList (0 : Fin 113) ++ [cellIdx e]) pr.2)
          = true := by
  intro e he hs
  have hp : (fun c =>
      !(winMem (0 : Fin 113) (coordOfC1 c)) && survivorB (0 : Fin 113) c)
      (cellIdx e) = true := by
    show (!(winMem (0 : Fin 113) (coordOfC1 (cellIdx e))) &&
      survivorB (0 : Fin 113) (cellIdx e)) = true
    rw [coordOfC1_cellIdx, he, hs]
    rfl
  have hmem : cellIdx e ∈ [72, 113] :=
    mem_of_filter_eq win_surv_0 (List.mem_range.mpr (cellIdx_lt e)) hp
  have hm' : cellIdx e = 72 ∨ cellIdx e = 113 := by simpa using hmem
  rcases hm' with hc | hc
  · rw [hc]
    exact win_sweepE_0_c72
  · rw [hc]
    exact win_sweepE_0_c113

theorem win_sweepP_0 :
    ∀ e₁ e₂ : G150 × Fin 2, winMem (0 : Fin 113) e₁ = false →
      winMem (0 : Fin 113) e₂ = false → e₁ ≠ e₂ →
      pairSurvivorB (0 : Fin 113) (cellIdx e₁) (cellIdx e₂) = true →
      ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [cellIdx e₁])
          ++ [cellIdx e₂]).length),
        syndFold ((winCellList (0 : Fin 113) ++ [cellIdx e₁]) ++ [cellIdx e₂])
          lam.val = 0 →
        ((tableEntries (0 : Fin 113) (cellIdx e₁))
            ++ tableEntries (0 : Fin 113) (cellIdx e₂)).any
          (fun pr => lam.val == localMaskOf
            ((winCellList (0 : Fin 113) ++ [cellIdx e₁]) ++ [cellIdx e₂]) pr.2)
          = true := by
  intro e₁ e₂ h₁ h₂ hne hp
  have hlt₁ := cellIdx_lt e₁
  have hlt₂ := cellIdx_lt e₂
  have hdiv : (cellIdx e₁ * 150 + cellIdx e₂) / 150 = cellIdx e₁ := by omega
  have hmod : (cellIdx e₁ * 150 + cellIdx e₂) % 150 = cellIdx e₂ := by omega
  have hcne : cellIdx e₁ ≠ cellIdx e₂ := fun h => hne (cellIdx_inj h)
  have hp' : (fun n =>
      !(n / 150 == n % 150) &&
      (!(winMem (0 : Fin 113) (coordOfC1 (n / 150))) &&
        (!(winMem (0 : Fin 113) (coordOfC1 (n % 150))) &&
          pairSurvivorB (0 : Fin 113) (n / 150) (n % 150))))
      (cellIdx e₁ * 150 + cellIdx e₂) = true := by
    show (!((cellIdx e₁ * 150 + cellIdx e₂) / 150 ==
        (cellIdx e₁ * 150 + cellIdx e₂) % 150) &&
      (!(winMem (0 : Fin 113)
          (coordOfC1 ((cellIdx e₁ * 150 + cellIdx e₂) / 150))) &&
        (!(winMem (0 : Fin 113)
            (coordOfC1 ((cellIdx e₁ * 150 + cellIdx e₂) % 150))) &&
          pairSurvivorB (0 : Fin 113)
            ((cellIdx e₁ * 150 + cellIdx e₂) / 150)
            ((cellIdx e₁ * 150 + cellIdx e₂) % 150)))) = true
    rw [hdiv, hmod, coordOfC1_cellIdx, coordOfC1_cellIdx, h₁, h₂, hp]
    simp [hcne]
  have hmem : cellIdx e₁ * 150 + cellIdx e₂ ∈ [1731, 10913, 12161, 12685, 12834, 17022] :=
    mem_of_filter_eq win_pairs_0 (List.mem_range.mpr (by omega)) hp'
  have hm' : cellIdx e₁ * 150 + cellIdx e₂ = 1731 ∨ cellIdx e₁ * 150 + cellIdx e₂ = 10913 ∨ cellIdx e₁ * 150 + cellIdx e₂ = 12161 ∨ cellIdx e₁ * 150 + cellIdx e₂ = 12685 ∨ cellIdx e₁ * 150 + cellIdx e₂ = 12834 ∨ cellIdx e₁ * 150 + cellIdx e₂ = 17022 := by simpa using hmem
  rcases hm' with hc | hc | hc | hc | hc | hc
  · have hc₁ : cellIdx e₁ = 11 := by omega
    have hc₂ : cellIdx e₂ = 81 := by omega
    rw [hc₁, hc₂]
    exact win_sweepP_0_p11_81
  · have hc₁ : cellIdx e₁ = 72 := by omega
    have hc₂ : cellIdx e₂ = 113 := by omega
    rw [hc₁, hc₂]
    exact win_sweepP_0_p72_113
  · have hc₁ : cellIdx e₁ = 81 := by omega
    have hc₂ : cellIdx e₂ = 11 := by omega
    rw [hc₁, hc₂]
    exact win_sweepP_0_p81_11
  · have hc₁ : cellIdx e₁ = 84 := by omega
    have hc₂ : cellIdx e₂ = 85 := by omega
    rw [hc₁, hc₂]
    exact win_sweepP_0_p84_85
  · have hc₁ : cellIdx e₁ = 85 := by omega
    have hc₂ : cellIdx e₂ = 84 := by omega
    rw [hc₁, hc₂]
    exact win_sweepP_0_p85_84
  · have hc₁ : cellIdx e₁ = 113 := by omega
    have hc₂ : cellIdx e₂ = 72 := by omega
    rw [hc₁, hc₂]
    exact win_sweepP_0_p113_72

theorem win_sweepE_1 :
    ∀ e : G150 × Fin 2, winMem (1 : Fin 113) e = false →
      survivorB (1 : Fin 113) (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [cellIdx e]).length),
        syndFold (winCellList (1 : Fin 113) ++ [cellIdx e]) lam.val = 0 →
        (tableEntries (1 : Fin 113) (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [cellIdx e]) pr.2)
          = true := by
  intro e he hs
  have hp : (fun c =>
      !(winMem (1 : Fin 113) (coordOfC1 c)) && survivorB (1 : Fin 113) c)
      (cellIdx e) = true := by
    show (!(winMem (1 : Fin 113) (coordOfC1 (cellIdx e))) &&
      survivorB (1 : Fin 113) (cellIdx e)) = true
    rw [coordOfC1_cellIdx, he, hs]
    rfl
  have hmem : cellIdx e ∈ [71, 73, 112, 140, 142] :=
    mem_of_filter_eq win_surv_1 (List.mem_range.mpr (cellIdx_lt e)) hp
  have hm' : cellIdx e = 71 ∨ cellIdx e = 73 ∨ cellIdx e = 112 ∨ cellIdx e = 140 ∨ cellIdx e = 142 := by simpa using hmem
  rcases hm' with hc | hc | hc | hc | hc
  · rw [hc]
    exact win_sweepE_1_c71
  · rw [hc]
    exact win_sweepE_1_c73
  · rw [hc]
    exact win_sweepE_1_c112
  · rw [hc]
    exact win_sweepE_1_c140
  · rw [hc]
    exact win_sweepE_1_c142

theorem win_sweepE_27 :
    ∀ e : G150 × Fin 2, winMem (27 : Fin 113) e = false →
      survivorB (27 : Fin 113) (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113) ++ [cellIdx e]).length),
        syndFold (winCellList (27 : Fin 113) ++ [cellIdx e]) lam.val = 0 →
        (tableEntries (27 : Fin 113) (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList (27 : Fin 113) ++ [cellIdx e]) pr.2)
          = true := by
  intro e he hs
  have hp : (fun c =>
      !(winMem (27 : Fin 113) (coordOfC1 c)) && survivorB (27 : Fin 113) c)
      (cellIdx e) = true := by
    show (!(winMem (27 : Fin 113) (coordOfC1 (cellIdx e))) &&
      survivorB (27 : Fin 113) (cellIdx e)) = true
    rw [coordOfC1_cellIdx, he, hs]
    rfl
  have hmem : cellIdx e ∈ [58, 99] :=
    mem_of_filter_eq win_surv_27 (List.mem_range.mpr (cellIdx_lt e)) hp
  have hm' : cellIdx e = 58 ∨ cellIdx e = 99 := by simpa using hmem
  rcases hm' with hc | hc
  · rw [hc]
    exact win_sweepE_27_c58
  · rw [hc]
    exact win_sweepE_27_c99

theorem win_sweepE_28 :
    ∀ e : G150 × Fin 2, winMem (28 : Fin 113) e = false →
      survivorB (28 : Fin 113) (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [cellIdx e]).length),
        syndFold (winCellList (28 : Fin 113) ++ [cellIdx e]) lam.val = 0 →
        (tableEntries (28 : Fin 113) (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [cellIdx e]) pr.2)
          = true := by
  intro e he hs
  have hp : (fun c =>
      !(winMem (28 : Fin 113) (coordOfC1 c)) && survivorB (28 : Fin 113) c)
      (cellIdx e) = true := by
    show (!(winMem (28 : Fin 113) (coordOfC1 (cellIdx e))) &&
      survivorB (28 : Fin 113) (cellIdx e)) = true
    rw [coordOfC1_cellIdx, he, hs]
    rfl
  have hmem : cellIdx e ∈ [47, 57, 98] :=
    mem_of_filter_eq win_surv_28 (List.mem_range.mpr (cellIdx_lt e)) hp
  have hm' : cellIdx e = 47 ∨ cellIdx e = 57 ∨ cellIdx e = 98 := by simpa using hmem
  rcases hm' with hc | hc | hc
  · rw [hc]
    exact win_sweepE_28_c47
  · rw [hc]
    exact win_sweepE_28_c57
  · rw [hc]
    exact win_sweepE_28_c98


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

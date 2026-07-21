/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window sweep leaves (2 of 7)

The per-class sweep certificates in the exact hypothesis shapes of
`window_sound_t1/t2/t3` (base sweeps, t = 1 classes [4, 30, 32, 49, 65]).

Each sweep's `native_decide` core is the falsifier filter
`(List.range (2 ^ L)).filter (syndrome-zero && not-in-table) = []`:
`List.filter` is a native tail-recursive stdlib loop, so only the
per-mask predicate is interpreted — a `Fin`-indexed ball is ~5× slower
per item and its `Decidable` instance overflows the C stack beyond
about `2 ^ 23`.  The flat `∀`-form the `window_sound_*` wrappers
consume is recovered through `forall_of_filter_nil`.
Files are parallel build leaves.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

private theorem win_len_4 :
    (winCellList (4 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_4_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (4 : Fin 113)) m == 0 &&
      !((tableEntries (4 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (4 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_4 :
    ∀ lam : Fin (2 ^ (winCellList (4 : Fin 113)).length),
      syndFold (winCellList (4 : Fin 113)) lam.val = 0 →
      (tableEntries (4 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (4 : Fin 113)) pr.2)
        = true := by
  rw [win_len_4]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (4 : Fin 113)) m)
    (fun m => (tableEntries (4 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (4 : Fin 113)) pr.2))
    win_sweep0_4_core

private theorem win_len_30 :
    (winCellList (30 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_30_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (30 : Fin 113)) m == 0 &&
      !((tableEntries (30 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (30 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_30 :
    ∀ lam : Fin (2 ^ (winCellList (30 : Fin 113)).length),
      syndFold (winCellList (30 : Fin 113)) lam.val = 0 →
      (tableEntries (30 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (30 : Fin 113)) pr.2)
        = true := by
  rw [win_len_30]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (30 : Fin 113)) m)
    (fun m => (tableEntries (30 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (30 : Fin 113)) pr.2))
    win_sweep0_30_core

private theorem win_len_32 :
    (winCellList (32 : Fin 113)).length = 22 := by
  native_decide

private theorem win_sweep0_32_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold (winCellList (32 : Fin 113)) m == 0 &&
      !((tableEntries (32 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (32 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_32 :
    ∀ lam : Fin (2 ^ (winCellList (32 : Fin 113)).length),
      syndFold (winCellList (32 : Fin 113)) lam.val = 0 →
      (tableEntries (32 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (32 : Fin 113)) pr.2)
        = true := by
  rw [win_len_32]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (32 : Fin 113)) m)
    (fun m => (tableEntries (32 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (32 : Fin 113)) pr.2))
    win_sweep0_32_core

private theorem win_len_49 :
    (winCellList (49 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_49_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (49 : Fin 113)) m == 0 &&
      !((tableEntries (49 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (49 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_49 :
    ∀ lam : Fin (2 ^ (winCellList (49 : Fin 113)).length),
      syndFold (winCellList (49 : Fin 113)) lam.val = 0 →
      (tableEntries (49 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (49 : Fin 113)) pr.2)
        = true := by
  rw [win_len_49]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (49 : Fin 113)) m)
    (fun m => (tableEntries (49 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (49 : Fin 113)) pr.2))
    win_sweep0_49_core

private theorem win_len_65 :
    (winCellList (65 : Fin 113)).length = 24 := by
  native_decide

private theorem win_sweep0_65_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (65 : Fin 113)) m == 0 &&
      !((tableEntries (65 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (65 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_65 :
    ∀ lam : Fin (2 ^ (winCellList (65 : Fin 113)).length),
      syndFold (winCellList (65 : Fin 113)) lam.val = 0 →
      (tableEntries (65 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (65 : Fin 113)) pr.2)
        = true := by
  rw [win_len_65]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (65 : Fin 113)) m)
    (fun m => (tableEntries (65 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (65 : Fin 113)) pr.2))
    win_sweep0_65_core


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

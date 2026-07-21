/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window sweep leaves (1 of 7)

The per-class sweep certificates in the exact hypothesis shapes of
`window_sound_t1/t2/t3` (base sweeps, t = 1 classes [26, 39, 56, 81]).

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

private theorem win_len_26 :
    (winCellList (26 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweep0_26_core :
    (List.range (2 ^ 23)).filter (fun m =>
      syndFold (winCellList (26 : Fin 113)) m == 0 &&
      !((tableEntries (26 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (26 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_26 :
    ∀ lam : Fin (2 ^ (winCellList (26 : Fin 113)).length),
      syndFold (winCellList (26 : Fin 113)) lam.val = 0 →
      (tableEntries (26 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (26 : Fin 113)) pr.2)
        = true := by
  rw [win_len_26]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (26 : Fin 113)) m)
    (fun m => (tableEntries (26 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (26 : Fin 113)) pr.2))
    win_sweep0_26_core

private theorem win_len_39 :
    (winCellList (39 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_39_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (39 : Fin 113)) m == 0 &&
      !((tableEntries (39 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (39 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_39 :
    ∀ lam : Fin (2 ^ (winCellList (39 : Fin 113)).length),
      syndFold (winCellList (39 : Fin 113)) lam.val = 0 →
      (tableEntries (39 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (39 : Fin 113)) pr.2)
        = true := by
  rw [win_len_39]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (39 : Fin 113)) m)
    (fun m => (tableEntries (39 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (39 : Fin 113)) pr.2))
    win_sweep0_39_core

private theorem win_len_56 :
    (winCellList (56 : Fin 113)).length = 24 := by
  native_decide

private theorem win_sweep0_56_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (56 : Fin 113)) m == 0 &&
      !((tableEntries (56 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (56 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_56 :
    ∀ lam : Fin (2 ^ (winCellList (56 : Fin 113)).length),
      syndFold (winCellList (56 : Fin 113)) lam.val = 0 →
      (tableEntries (56 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (56 : Fin 113)) pr.2)
        = true := by
  rw [win_len_56]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (56 : Fin 113)) m)
    (fun m => (tableEntries (56 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (56 : Fin 113)) pr.2))
    win_sweep0_56_core

private theorem win_len_81 :
    (winCellList (81 : Fin 113)).length = 26 := by
  native_decide

private theorem win_sweep0_81_core :
    (List.range (2 ^ 26)).filter (fun m =>
      syndFold (winCellList (81 : Fin 113)) m == 0 &&
      !((tableEntries (81 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (81 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_81 :
    ∀ lam : Fin (2 ^ (winCellList (81 : Fin 113)).length),
      syndFold (winCellList (81 : Fin 113)) lam.val = 0 →
      (tableEntries (81 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (81 : Fin 113)) pr.2)
        = true := by
  rw [win_len_81]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (81 : Fin 113)) m)
    (fun m => (tableEntries (81 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (81 : Fin 113)) pr.2))
    win_sweep0_81_core


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window sweep leaves (3 of 7)

The per-class sweep certificates in the exact hypothesis shapes of
`window_sound_t1/t2/t3` (base sweeps, t = 1 classes [24, 25, 29, 37, 38, 50]).

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

private theorem win_len_24 :
    (winCellList (24 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweep0_24_core :
    (List.range (2 ^ 23)).filter (fun m =>
      syndFold (winCellList (24 : Fin 113)) m == 0 &&
      !((tableEntries (24 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (24 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_24 :
    ∀ lam : Fin (2 ^ (winCellList (24 : Fin 113)).length),
      syndFold (winCellList (24 : Fin 113)) lam.val = 0 →
      (tableEntries (24 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (24 : Fin 113)) pr.2)
        = true := by
  rw [win_len_24]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (24 : Fin 113)) m)
    (fun m => (tableEntries (24 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (24 : Fin 113)) pr.2))
    win_sweep0_24_core

private theorem win_len_25 :
    (winCellList (25 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweep0_25_core :
    (List.range (2 ^ 23)).filter (fun m =>
      syndFold (winCellList (25 : Fin 113)) m == 0 &&
      !((tableEntries (25 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (25 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_25 :
    ∀ lam : Fin (2 ^ (winCellList (25 : Fin 113)).length),
      syndFold (winCellList (25 : Fin 113)) lam.val = 0 →
      (tableEntries (25 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (25 : Fin 113)) pr.2)
        = true := by
  rw [win_len_25]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (25 : Fin 113)) m)
    (fun m => (tableEntries (25 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (25 : Fin 113)) pr.2))
    win_sweep0_25_core

private theorem win_len_29 :
    (winCellList (29 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_29_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (29 : Fin 113)) m == 0 &&
      !((tableEntries (29 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (29 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_29 :
    ∀ lam : Fin (2 ^ (winCellList (29 : Fin 113)).length),
      syndFold (winCellList (29 : Fin 113)) lam.val = 0 →
      (tableEntries (29 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (29 : Fin 113)) pr.2)
        = true := by
  rw [win_len_29]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (29 : Fin 113)) m)
    (fun m => (tableEntries (29 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (29 : Fin 113)) pr.2))
    win_sweep0_29_core

private theorem win_len_37 :
    (winCellList (37 : Fin 113)).length = 22 := by
  native_decide

private theorem win_sweep0_37_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold (winCellList (37 : Fin 113)) m == 0 &&
      !((tableEntries (37 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (37 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_37 :
    ∀ lam : Fin (2 ^ (winCellList (37 : Fin 113)).length),
      syndFold (winCellList (37 : Fin 113)) lam.val = 0 →
      (tableEntries (37 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (37 : Fin 113)) pr.2)
        = true := by
  rw [win_len_37]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (37 : Fin 113)) m)
    (fun m => (tableEntries (37 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (37 : Fin 113)) pr.2))
    win_sweep0_37_core

private theorem win_len_38 :
    (winCellList (38 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_38_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (38 : Fin 113)) m == 0 &&
      !((tableEntries (38 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (38 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_38 :
    ∀ lam : Fin (2 ^ (winCellList (38 : Fin 113)).length),
      syndFold (winCellList (38 : Fin 113)) lam.val = 0 →
      (tableEntries (38 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (38 : Fin 113)) pr.2)
        = true := by
  rw [win_len_38]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (38 : Fin 113)) m)
    (fun m => (tableEntries (38 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (38 : Fin 113)) pr.2))
    win_sweep0_38_core

private theorem win_len_50 :
    (winCellList (50 : Fin 113)).length = 25 := by
  native_decide

private theorem win_sweep0_50_core :
    (List.range (2 ^ 25)).filter (fun m =>
      syndFold (winCellList (50 : Fin 113)) m == 0 &&
      !((tableEntries (50 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (50 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_50 :
    ∀ lam : Fin (2 ^ (winCellList (50 : Fin 113)).length),
      syndFold (winCellList (50 : Fin 113)) lam.val = 0 →
      (tableEntries (50 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (50 : Fin 113)) pr.2)
        = true := by
  rw [win_len_50]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (50 : Fin 113)) m)
    (fun m => (tableEntries (50 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (50 : Fin 113)) pr.2))
    win_sweep0_50_core


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window sweep leaves (4 of 7)

The per-class sweep certificates in the exact hypothesis shapes of
`window_sound_t1/t2/t3` (extension sweeps of class 1 (5 surviving cells)).

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

private theorem win_len_1 :
    (winCellList (1 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweepE_1_c71_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (1 : Fin 113) ++ [71]) m == 0 &&
      !((tableEntries (1 : Fin 113) 71).any (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [71]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_1_c71 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [71]).length),
      syndFold (winCellList (1 : Fin 113) ++ [71]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 71).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [71]) pr.2)
        = true := by
  have hlen : (winCellList (1 : Fin 113) ++ [71]).length = 24 := by
    have h := win_len_1
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (1 : Fin 113) ++ [71]) m)
    (fun m => (tableEntries (1 : Fin 113) 71).any
      (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [71]) pr.2))
    win_sweepE_1_c71_core

private theorem win_sweepE_1_c73_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (1 : Fin 113) ++ [73]) m == 0 &&
      !((tableEntries (1 : Fin 113) 73).any (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_1_c73 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [73]).length),
      syndFold (winCellList (1 : Fin 113) ++ [73]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 73).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2)
        = true := by
  have hlen : (winCellList (1 : Fin 113) ++ [73]).length = 24 := by
    have h := win_len_1
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (1 : Fin 113) ++ [73]) m)
    (fun m => (tableEntries (1 : Fin 113) 73).any
      (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2))
    win_sweepE_1_c73_core

private theorem win_sweepE_1_c112_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (1 : Fin 113) ++ [112]) m == 0 &&
      !((tableEntries (1 : Fin 113) 112).any (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [112]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_1_c112 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [112]).length),
      syndFold (winCellList (1 : Fin 113) ++ [112]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 112).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [112]) pr.2)
        = true := by
  have hlen : (winCellList (1 : Fin 113) ++ [112]).length = 24 := by
    have h := win_len_1
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (1 : Fin 113) ++ [112]) m)
    (fun m => (tableEntries (1 : Fin 113) 112).any
      (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [112]) pr.2))
    win_sweepE_1_c112_core

private theorem win_sweepE_1_c140_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (1 : Fin 113) ++ [140]) m == 0 &&
      !((tableEntries (1 : Fin 113) 140).any (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [140]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_1_c140 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [140]).length),
      syndFold (winCellList (1 : Fin 113) ++ [140]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 140).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [140]) pr.2)
        = true := by
  have hlen : (winCellList (1 : Fin 113) ++ [140]).length = 24 := by
    have h := win_len_1
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (1 : Fin 113) ++ [140]) m)
    (fun m => (tableEntries (1 : Fin 113) 140).any
      (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [140]) pr.2))
    win_sweepE_1_c140_core

private theorem win_sweepE_1_c142_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (1 : Fin 113) ++ [142]) m == 0 &&
      !((tableEntries (1 : Fin 113) 142).any (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [142]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_1_c142 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [142]).length),
      syndFold (winCellList (1 : Fin 113) ++ [142]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 142).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [142]) pr.2)
        = true := by
  have hlen : (winCellList (1 : Fin 113) ++ [142]).length = 24 := by
    have h := win_len_1
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (1 : Fin 113) ++ [142]) m)
    (fun m => (tableEntries (1 : Fin 113) 142).any
      (fun pr => m == localMaskOf (winCellList (1 : Fin 113) ++ [142]) pr.2))
    win_sweepE_1_c142_core


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

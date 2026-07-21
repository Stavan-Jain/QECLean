/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window sweep leaves (5 of 7)

The per-class sweep certificates in the exact hypothesis shapes of
`window_sound_t1/t2/t3` (extension sweeps of classes [0, 27, 28]).

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

private theorem win_len_0 :
    (winCellList (0 : Fin 113)).length = 20 := by
  native_decide

private theorem win_sweepE_0_c72_core :
    (List.range (2 ^ 21)).filter (fun m =>
      syndFold (winCellList (0 : Fin 113) ++ [72]) m == 0 &&
      !((tableEntries (0 : Fin 113) 72).any (fun pr => m == localMaskOf (winCellList (0 : Fin 113) ++ [72]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_0_c72 :
    ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113) ++ [72]).length),
      syndFold (winCellList (0 : Fin 113) ++ [72]) lam.val = 0 →
      (tableEntries (0 : Fin 113) 72).any
        (fun pr => lam.val == localMaskOf (winCellList (0 : Fin 113) ++ [72]) pr.2)
        = true := by
  have hlen : (winCellList (0 : Fin 113) ++ [72]).length = 21 := by
    have h := win_len_0
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (0 : Fin 113) ++ [72]) m)
    (fun m => (tableEntries (0 : Fin 113) 72).any
      (fun pr => m == localMaskOf (winCellList (0 : Fin 113) ++ [72]) pr.2))
    win_sweepE_0_c72_core

private theorem win_sweepE_0_c113_core :
    (List.range (2 ^ 21)).filter (fun m =>
      syndFold (winCellList (0 : Fin 113) ++ [113]) m == 0 &&
      !((tableEntries (0 : Fin 113) 113).any (fun pr => m == localMaskOf (winCellList (0 : Fin 113) ++ [113]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_0_c113 :
    ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113) ++ [113]).length),
      syndFold (winCellList (0 : Fin 113) ++ [113]) lam.val = 0 →
      (tableEntries (0 : Fin 113) 113).any
        (fun pr => lam.val == localMaskOf (winCellList (0 : Fin 113) ++ [113]) pr.2)
        = true := by
  have hlen : (winCellList (0 : Fin 113) ++ [113]).length = 21 := by
    have h := win_len_0
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (0 : Fin 113) ++ [113]) m)
    (fun m => (tableEntries (0 : Fin 113) 113).any
      (fun pr => m == localMaskOf (winCellList (0 : Fin 113) ++ [113]) pr.2))
    win_sweepE_0_c113_core

private theorem win_len_27 :
    (winCellList (27 : Fin 113)).length = 21 := by
  native_decide

private theorem win_sweepE_27_c58_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold (winCellList (27 : Fin 113) ++ [58]) m == 0 &&
      !((tableEntries (27 : Fin 113) 58).any (fun pr => m == localMaskOf (winCellList (27 : Fin 113) ++ [58]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_27_c58 :
    ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113) ++ [58]).length),
      syndFold (winCellList (27 : Fin 113) ++ [58]) lam.val = 0 →
      (tableEntries (27 : Fin 113) 58).any
        (fun pr => lam.val == localMaskOf (winCellList (27 : Fin 113) ++ [58]) pr.2)
        = true := by
  have hlen : (winCellList (27 : Fin 113) ++ [58]).length = 22 := by
    have h := win_len_27
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (27 : Fin 113) ++ [58]) m)
    (fun m => (tableEntries (27 : Fin 113) 58).any
      (fun pr => m == localMaskOf (winCellList (27 : Fin 113) ++ [58]) pr.2))
    win_sweepE_27_c58_core

private theorem win_sweepE_27_c99_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold (winCellList (27 : Fin 113) ++ [99]) m == 0 &&
      !((tableEntries (27 : Fin 113) 99).any (fun pr => m == localMaskOf (winCellList (27 : Fin 113) ++ [99]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_27_c99 :
    ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113) ++ [99]).length),
      syndFold (winCellList (27 : Fin 113) ++ [99]) lam.val = 0 →
      (tableEntries (27 : Fin 113) 99).any
        (fun pr => lam.val == localMaskOf (winCellList (27 : Fin 113) ++ [99]) pr.2)
        = true := by
  have hlen : (winCellList (27 : Fin 113) ++ [99]).length = 22 := by
    have h := win_len_27
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (27 : Fin 113) ++ [99]) m)
    (fun m => (tableEntries (27 : Fin 113) 99).any
      (fun pr => m == localMaskOf (winCellList (27 : Fin 113) ++ [99]) pr.2))
    win_sweepE_27_c99_core

private theorem win_len_28 :
    (winCellList (28 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweepE_28_c47_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (28 : Fin 113) ++ [47]) m == 0 &&
      !((tableEntries (28 : Fin 113) 47).any (fun pr => m == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_28_c47 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [47]).length),
      syndFold (winCellList (28 : Fin 113) ++ [47]) lam.val = 0 →
      (tableEntries (28 : Fin 113) 47).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2)
        = true := by
  have hlen : (winCellList (28 : Fin 113) ++ [47]).length = 24 := by
    have h := win_len_28
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (28 : Fin 113) ++ [47]) m)
    (fun m => (tableEntries (28 : Fin 113) 47).any
      (fun pr => m == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2))
    win_sweepE_28_c47_core

private theorem win_sweepE_28_c57_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (28 : Fin 113) ++ [57]) m == 0 &&
      !((tableEntries (28 : Fin 113) 57).any (fun pr => m == localMaskOf (winCellList (28 : Fin 113) ++ [57]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_28_c57 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [57]).length),
      syndFold (winCellList (28 : Fin 113) ++ [57]) lam.val = 0 →
      (tableEntries (28 : Fin 113) 57).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [57]) pr.2)
        = true := by
  have hlen : (winCellList (28 : Fin 113) ++ [57]).length = 24 := by
    have h := win_len_28
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (28 : Fin 113) ++ [57]) m)
    (fun m => (tableEntries (28 : Fin 113) 57).any
      (fun pr => m == localMaskOf (winCellList (28 : Fin 113) ++ [57]) pr.2))
    win_sweepE_28_c57_core

private theorem win_sweepE_28_c98_core :
    (List.range (2 ^ 24)).filter (fun m =>
      syndFold (winCellList (28 : Fin 113) ++ [98]) m == 0 &&
      !((tableEntries (28 : Fin 113) 98).any (fun pr => m == localMaskOf (winCellList (28 : Fin 113) ++ [98]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepE_28_c98 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [98]).length),
      syndFold (winCellList (28 : Fin 113) ++ [98]) lam.val = 0 →
      (tableEntries (28 : Fin 113) 98).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [98]) pr.2)
        = true := by
  have hlen : (winCellList (28 : Fin 113) ++ [98]).length = 24 := by
    have h := win_len_28
    rw [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (28 : Fin 113) ++ [98]) m)
    (fun m => (tableEntries (28 : Fin 113) 98).any
      (fun pr => m == localMaskOf (winCellList (28 : Fin 113) ++ [98]) pr.2))
    win_sweepE_28_c98_core


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

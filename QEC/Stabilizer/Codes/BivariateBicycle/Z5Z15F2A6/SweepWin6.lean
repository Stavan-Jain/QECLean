/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.WindowEngine

/-!
# Z5Z15F2A6 window sweep leaves (6 of 7)

The per-class sweep certificates in the exact hypothesis shapes of
`window_sound_t1/t2/t3` (base sweeps of the t >= 2 classes, and the t = 3 pair sweeps).

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

private theorem win_sweep0_0_core :
    (List.range (2 ^ 20)).filter (fun m =>
      syndFold (winCellList (0 : Fin 113)) m == 0 &&
      !((tableEntries (0 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (0 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_0 :
    ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113)).length),
      syndFold (winCellList (0 : Fin 113)) lam.val = 0 →
      (tableEntries (0 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (0 : Fin 113)) pr.2)
        = true := by
  rw [win_len_0]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (0 : Fin 113)) m)
    (fun m => (tableEntries (0 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (0 : Fin 113)) pr.2))
    win_sweep0_0_core

private theorem win_sweepP_0_p11_81_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) m == 0 &&
      !(((tableEntries (0 : Fin 113) 11) ++ tableEntries (0 : Fin 113) 81).any (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepP_0_p11_81 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [11]) ++ [81]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 11) ++ tableEntries (0 : Fin 113) 81).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) pr.2)
        = true := by
  have hlen : ((winCellList (0 : Fin 113) ++ [11]) ++ [81]).length = 22 := by
    have h := win_len_0
    rw [List.length_append, List.length_append,
      List.length_singleton, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) m)
    (fun m => ((tableEntries (0 : Fin 113) 11) ++ tableEntries (0 : Fin 113) 81).any
      (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) pr.2))
    win_sweepP_0_p11_81_core

private theorem win_sweepP_0_p72_113_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) m == 0 &&
      !(((tableEntries (0 : Fin 113) 72) ++ tableEntries (0 : Fin 113) 113).any (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepP_0_p72_113 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [72]) ++ [113]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 72) ++ tableEntries (0 : Fin 113) 113).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) pr.2)
        = true := by
  have hlen : ((winCellList (0 : Fin 113) ++ [72]) ++ [113]).length = 22 := by
    have h := win_len_0
    rw [List.length_append, List.length_append,
      List.length_singleton, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) m)
    (fun m => ((tableEntries (0 : Fin 113) 72) ++ tableEntries (0 : Fin 113) 113).any
      (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) pr.2))
    win_sweepP_0_p72_113_core

private theorem win_sweepP_0_p81_11_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) m == 0 &&
      !(((tableEntries (0 : Fin 113) 81) ++ tableEntries (0 : Fin 113) 11).any (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepP_0_p81_11 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [81]) ++ [11]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 81) ++ tableEntries (0 : Fin 113) 11).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) pr.2)
        = true := by
  have hlen : ((winCellList (0 : Fin 113) ++ [81]) ++ [11]).length = 22 := by
    have h := win_len_0
    rw [List.length_append, List.length_append,
      List.length_singleton, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) m)
    (fun m => ((tableEntries (0 : Fin 113) 81) ++ tableEntries (0 : Fin 113) 11).any
      (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) pr.2))
    win_sweepP_0_p81_11_core

private theorem win_sweepP_0_p84_85_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) m == 0 &&
      !(((tableEntries (0 : Fin 113) 84) ++ tableEntries (0 : Fin 113) 85).any (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepP_0_p84_85 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [84]) ++ [85]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 84) ++ tableEntries (0 : Fin 113) 85).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) pr.2)
        = true := by
  have hlen : ((winCellList (0 : Fin 113) ++ [84]) ++ [85]).length = 22 := by
    have h := win_len_0
    rw [List.length_append, List.length_append,
      List.length_singleton, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) m)
    (fun m => ((tableEntries (0 : Fin 113) 84) ++ tableEntries (0 : Fin 113) 85).any
      (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) pr.2))
    win_sweepP_0_p84_85_core

private theorem win_sweepP_0_p85_84_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) m == 0 &&
      !(((tableEntries (0 : Fin 113) 85) ++ tableEntries (0 : Fin 113) 84).any (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepP_0_p85_84 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [85]) ++ [84]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 85) ++ tableEntries (0 : Fin 113) 84).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) pr.2)
        = true := by
  have hlen : ((winCellList (0 : Fin 113) ++ [85]) ++ [84]).length = 22 := by
    have h := win_len_0
    rw [List.length_append, List.length_append,
      List.length_singleton, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) m)
    (fun m => ((tableEntries (0 : Fin 113) 85) ++ tableEntries (0 : Fin 113) 84).any
      (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) pr.2))
    win_sweepP_0_p85_84_core

private theorem win_sweepP_0_p113_72_core :
    (List.range (2 ^ 22)).filter (fun m =>
      syndFold ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) m == 0 &&
      !(((tableEntries (0 : Fin 113) 113) ++ tableEntries (0 : Fin 113) 72).any (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) pr.2)))
      = [] := by
  native_decide

theorem win_sweepP_0_p113_72 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [113]) ++ [72]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 113) ++ tableEntries (0 : Fin 113) 72).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) pr.2)
        = true := by
  have hlen : ((winCellList (0 : Fin 113) ++ [113]) ++ [72]).length = 22 := by
    have h := win_len_0
    rw [List.length_append, List.length_append,
      List.length_singleton, List.length_singleton]
    omega
  rw [hlen]
  exact forall_of_filter_nil
    (fun m => syndFold ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) m)
    (fun m => ((tableEntries (0 : Fin 113) 113) ++ tableEntries (0 : Fin 113) 72).any
      (fun pr => m == localMaskOf ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) pr.2))
    win_sweepP_0_p113_72_core

private theorem win_len_1 :
    (winCellList (1 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweep0_1_core :
    (List.range (2 ^ 23)).filter (fun m =>
      syndFold (winCellList (1 : Fin 113)) m == 0 &&
      !((tableEntries (1 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (1 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_1 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113)).length),
      syndFold (winCellList (1 : Fin 113)) lam.val = 0 →
      (tableEntries (1 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113)) pr.2)
        = true := by
  rw [win_len_1]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (1 : Fin 113)) m)
    (fun m => (tableEntries (1 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (1 : Fin 113)) pr.2))
    win_sweep0_1_core

private theorem win_len_27 :
    (winCellList (27 : Fin 113)).length = 21 := by
  native_decide

private theorem win_sweep0_27_core :
    (List.range (2 ^ 21)).filter (fun m =>
      syndFold (winCellList (27 : Fin 113)) m == 0 &&
      !((tableEntries (27 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (27 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_27 :
    ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113)).length),
      syndFold (winCellList (27 : Fin 113)) lam.val = 0 →
      (tableEntries (27 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (27 : Fin 113)) pr.2)
        = true := by
  rw [win_len_27]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (27 : Fin 113)) m)
    (fun m => (tableEntries (27 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (27 : Fin 113)) pr.2))
    win_sweep0_27_core

private theorem win_len_28 :
    (winCellList (28 : Fin 113)).length = 23 := by
  native_decide

private theorem win_sweep0_28_core :
    (List.range (2 ^ 23)).filter (fun m =>
      syndFold (winCellList (28 : Fin 113)) m == 0 &&
      !((tableEntries (28 : Fin 113) 150).any (fun pr => m == localMaskOf (winCellList (28 : Fin 113)) pr.2)))
      = [] := by
  native_decide

theorem win_sweep0_28 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113)).length),
      syndFold (winCellList (28 : Fin 113)) lam.val = 0 →
      (tableEntries (28 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113)) pr.2)
        = true := by
  rw [win_len_28]
  exact forall_of_filter_nil
    (fun m => syndFold (winCellList (28 : Fin 113)) m)
    (fun m => (tableEntries (28 : Fin 113) 150).any
      (fun pr => m == localMaskOf (winCellList (28 : Fin 113)) pr.2))
    win_sweep0_28_core


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

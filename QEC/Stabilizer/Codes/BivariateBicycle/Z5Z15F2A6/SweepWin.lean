/-
GENERATED FILE — DO NOT HAND-EDIT.
Generator: qec-lab:experiments/bb_lab/scripts/gen_f2a6_dangerous_lean.py
Data source: qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl
Regen: cd experiments/bb_lab && uv run python scripts/gen_f2a6_dangerous_lean.py --force
-/

import Mathlib.Tactic.FinCases
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.KernelCert

/-!
# Z5Z15F2A6 window sweeps via pivot certificates

Every sweep obligation of `window_sound_t1/t2/t3` — base sweeps of the
19 window classes, extension sweeps of the surviving extra cells, and
the t = 3 pair sweeps — discharged by Gaussian-elimination pivot
certificates instead of `2^L` mask enumeration.

Per system, one `native_decide` checks (`cert1B`/`cert2B`) that the
tabulated pivot order triangularizes the window's syndrome map and that
the tabulated kernel generators are δ-normalized on the free positions;
`kernel_classify_dim1/dim2` then classifies every zero-syndrome mask
into the generator span, and membership of each span element in the
candidate table is a second tabulated check.  The public theorem
statements are byte-identical to the enumeration versions.

`survivorB`/`pairSurvivorB` pass for only finitely many extra cells per
t ≥ 2 class; one cheap `native_decide` certifies each survivor list, and
the public `win_sweepE_*`/`win_sweepP_*` theorems dispatch through
`mem_of_filter_eq` to the per-survivor flats.  No sweep quantifier ever
puts a ball behind a `Decidable` arrow instance.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

private theorem win_sweep0_4_cert :
    (((winCellList (4 : Fin 113)).length == 25)
      && (cert1B (winCellList (4 : Fin 113))
        [(20, 61), (1, 62), (7, 1), (5, 16), (6, 2), (8, 19), (11, 13), (4, 28), (9, 7), (12, 21),
     (13, 22), (14, 23), (15, 24), (10, 25), (2, 10), (3, 11), (16, 36), (17, 38), (18, 51), (19,
     52), (21, 4), (22, 5), (23, 6), (24, 8)]
        0 24119807)
      && ((tableEntries (4 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (4 : Fin 113)) pr.2))
      && ((tableEntries (4 : Fin 113) 150).any (fun pr => 24119807 == localMaskOf (winCellList (4 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_4 :
    ∀ lam : Fin (2 ^ (winCellList (4 : Fin 113)).length),
      syndFold (winCellList (4 : Fin 113)) lam.val = 0 →
      (tableEntries (4 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (4 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_4_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (4 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_24_cert :
    (((winCellList (24 : Fin 113)).length == 23)
      && (cert1B (winCellList (24 : Fin 113))
        [(5, 0), (7, 21), (2, 7), (1, 61), (17, 3), (3, 63), (18, 4), (20, 6), (19, 66), (4, 65),
     (6, 5), (21, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 23), (13, 25), (14, 38), (15, 39),
     (16, 53), (22, 12)]
        0 6162687)
      && ((tableEntries (24 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (24 : Fin 113)) pr.2))
      && ((tableEntries (24 : Fin 113) 150).any (fun pr => 6162687 == localMaskOf (winCellList (24 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_24 :
    ∀ lam : Fin (2 ^ (winCellList (24 : Fin 113)).length),
      syndFold (winCellList (24 : Fin 113)) lam.val = 0 →
      (tableEntries (24 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (24 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_24_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (24 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_25_cert :
    (((winCellList (25 : Fin 113)).length == 23)
      && (cert1B (winCellList (25 : Fin 113))
        [(1, 73), (7, 4), (5, 18), (11, 12), (17, 0), (2, 60), (18, 1), (19, 3), (3, 63), (21, 6),
     (20, 66), (4, 65), (6, 5), (10, 11), (9, 10), (8, 9), (12, 23), (13, 25), (14, 38), (15, 39),
     (16, 53), (22, 8)]
        0 4065535)
      && ((tableEntries (25 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (25 : Fin 113)) pr.2))
      && ((tableEntries (25 : Fin 113) 150).any (fun pr => 4065535 == localMaskOf (winCellList (25 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_25 :
    ∀ lam : Fin (2 ^ (winCellList (25 : Fin 113)).length),
      syndFold (winCellList (25 : Fin 113)) lam.val = 0 →
      (tableEntries (25 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (25 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_25_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (25 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_26_cert :
    (((winCellList (26 : Fin 113)).length == 23)
      && (cert1B (winCellList (26 : Fin 113))
        [(17, 0), (1, 61), (5, 3), (7, 20), (19, 6), (3, 67), (2, 63), (18, 66), (4, 65), (6, 5),
     (20, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 23), (13, 25), (14, 38), (15, 39), (16,
     53), (21, 12), (22, 14)]
        0 7211263)
      && ((tableEntries (26 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (26 : Fin 113)) pr.2))
      && ((tableEntries (26 : Fin 113) 150).any (fun pr => 7211263 == localMaskOf (winCellList (26 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_26 :
    ∀ lam : Fin (2 ^ (winCellList (26 : Fin 113)).length),
      syndFold (winCellList (26 : Fin 113)) lam.val = 0 →
      (tableEntries (26 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (26 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_26_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (26 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_29_cert :
    (((winCellList (29 : Fin 113)).length == 25)
      && (cert1B (winCellList (29 : Fin 113))
        [(23, 73), (1, 72), (5, 12), (7, 3), (6, 17), (12, 29), (18, 0), (19, 2), (2, 63), (3,
     62), (20, 5), (4, 65), (11, 11), (10, 10), (9, 9), (13, 23), (8, 22), (14, 24), (15, 37),
     (16, 38), (17, 52), (21, 7), (22, 8), (24, 14)]
        0 27005183)
      && ((tableEntries (29 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (29 : Fin 113)) pr.2))
      && ((tableEntries (29 : Fin 113) 150).any (fun pr => 27005183 == localMaskOf (winCellList (29 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_29 :
    ∀ lam : Fin (2 ^ (winCellList (29 : Fin 113)).length),
      syndFold (winCellList (29 : Fin 113)) lam.val = 0 →
      (tableEntries (29 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (29 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_29_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (29 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_30_cert :
    (((winCellList (30 : Fin 113)).length == 25)
      && (cert1B (winCellList (30 : Fin 113))
        [(12, 0), (5, 29), (6, 14), (7, 20), (2, 6), (1, 60), (18, 2), (3, 62), (19, 3), (20, 5),
     (4, 65), (22, 69), (21, 68), (8, 7), (9, 8), (10, 9), (11, 10), (13, 22), (14, 24), (15, 37),
     (16, 38), (17, 52), (23, 11), (24, 12)]
        0 27005183)
      && ((tableEntries (30 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (30 : Fin 113)) pr.2))
      && ((tableEntries (30 : Fin 113) 150).any (fun pr => 27005183 == localMaskOf (winCellList (30 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_30 :
    ∀ lam : Fin (2 ^ (winCellList (30 : Fin 113)).length),
      syndFold (winCellList (30 : Fin 113)) lam.val = 0 →
      (tableEntries (30 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (30 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_30_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (30 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_32_cert :
    (((winCellList (32 : Fin 113)).length == 22)
      && (cert1B (winCellList (32 : Fin 113))
        [(16, 0), (1, 61), (2, 60), (3, 64), (5, 3), (18, 6), (17, 66), (4, 65), (6, 5), (19, 7),
     (20, 69), (7, 8), (8, 9), (9, 10), (10, 11), (11, 23), (12, 25), (13, 38), (14, 39), (15,
     53), (21, 12)]
        0 3081599)
      && ((tableEntries (32 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (32 : Fin 113)) pr.2))
      && ((tableEntries (32 : Fin 113) 150).any (fun pr => 3081599 == localMaskOf (winCellList (32 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_32 :
    ∀ lam : Fin (2 ^ (winCellList (32 : Fin 113)).length),
      syndFold (winCellList (32 : Fin 113)) lam.val = 0 →
      (tableEntries (32 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (32 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_32_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (32 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_37_cert :
    (((winCellList (37 : Fin 113)).length == 22)
      && (cert1B (winCellList (37 : Fin 113))
        [(16, 0), (1, 61), (2, 60), (5, 6), (17, 2), (3, 62), (18, 3), (19, 66), (4, 65), (6, 5),
     (20, 69), (7, 8), (8, 9), (9, 10), (10, 11), (11, 23), (12, 25), (13, 38), (14, 39), (15,
     53), (21, 12)]
        0 3081471)
      && ((tableEntries (37 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (37 : Fin 113)) pr.2))
      && ((tableEntries (37 : Fin 113) 150).any (fun pr => 3081471 == localMaskOf (winCellList (37 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_37 :
    ∀ lam : Fin (2 ^ (winCellList (37 : Fin 113)).length),
      syndFold (winCellList (37 : Fin 113)) lam.val = 0 →
      (tableEntries (37 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (37 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_37_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (37 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_38_cert :
    (((winCellList (38 : Fin 113)).length == 25)
      && (cert1B (winCellList (38 : Fin 113))
        [(20, 62), (1, 63), (6, 5), (7, 1), (5, 16), (11, 14), (4, 28), (21, 4), (2, 64), (3, 65),
     (10, 10), (15, 25), (14, 24), (13, 23), (16, 37), (12, 36), (8, 21), (9, 7), (17, 38), (18,
     51), (19, 52), (22, 6), (23, 8), (24, 13)]
        0 28314367)
      && ((tableEntries (38 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (38 : Fin 113)) pr.2))
      && ((tableEntries (38 : Fin 113) 150).any (fun pr => 28314367 == localMaskOf (winCellList (38 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_38 :
    ∀ lam : Fin (2 ^ (winCellList (38 : Fin 113)).length),
      syndFold (winCellList (38 : Fin 113)) lam.val = 0 →
      (tableEntries (38 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (38 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_38_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (38 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_39_cert :
    (((winCellList (39 : Fin 113)).length == 25)
      && (cert1B (winCellList (39 : Fin 113))
        [(16, 49), (1, 50), (18, 53), (20, 64), (4, 4), (3, 73), (5, 65), (7, 0), (6, 15), (2,
     13), (19, 1), (22, 68), (21, 67), (8, 6), (9, 7), (10, 8), (12, 21), (13, 23), (11, 24), (14,
     36), (15, 37), (17, 51), (23, 9), (24, 10)]
        0 14483711)
      && ((tableEntries (39 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (39 : Fin 113)) pr.2))
      && ((tableEntries (39 : Fin 113) 150).any (fun pr => 14483711 == localMaskOf (winCellList (39 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_39 :
    ∀ lam : Fin (2 ^ (winCellList (39 : Fin 113)).length),
      syndFold (winCellList (39 : Fin 113)) lam.val = 0 →
      (tableEntries (39 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (39 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_39_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (39 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_49_cert :
    (((winCellList (49 : Fin 113)).length == 25)
      && (cert1B (winCellList (49 : Fin 113))
        [(16, 49), (1, 50), (18, 53), (19, 64), (5, 65), (4, 61), (7, 3), (6, 18), (3, 1), (21,
     68), (22, 70), (2, 71), (11, 10), (10, 9), (9, 8), (8, 7), (12, 21), (13, 23), (14, 36), (15,
     37), (17, 51), (20, 6), (23, 12), (24, 13)]
        0 28115199)
      && ((tableEntries (49 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (49 : Fin 113)) pr.2))
      && ((tableEntries (49 : Fin 113) 150).any (fun pr => 28115199 == localMaskOf (winCellList (49 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_49 :
    ∀ lam : Fin (2 ^ (winCellList (49 : Fin 113)).length),
      syndFold (winCellList (49 : Fin 113)) lam.val = 0 →
      (tableEntries (49 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (49 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_49_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (49 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_50_cert :
    (((winCellList (50 : Fin 113)).length == 25)
      && (cert1B (winCellList (50 : Fin 113))
        [(16, 49), (1, 50), (18, 53), (21, 64), (5, 65), (7, 4), (4, 5), (3, 74), (6, 19), (2,
     13), (19, 1), (20, 2), (23, 68), (22, 67), (8, 6), (9, 7), (10, 8), (11, 9), (12, 21), (13,
     23), (14, 36), (15, 37), (17, 51), (24, 10)]
        0 12386559)
      && ((tableEntries (50 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (50 : Fin 113)) pr.2))
      && ((tableEntries (50 : Fin 113) 150).any (fun pr => 12386559 == localMaskOf (winCellList (50 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_50 :
    ∀ lam : Fin (2 ^ (winCellList (50 : Fin 113)).length),
      syndFold (winCellList (50 : Fin 113)) lam.val = 0 →
      (tableEntries (50 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (50 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_50_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (50 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_56_cert :
    (((winCellList (56 : Fin 113)).length == 24)
      && (cert1B (winCellList (56 : Fin 113))
        [(15, 49), (1, 50), (17, 53), (18, 64), (4, 4), (5, 62), (19, 65), (6, 5), (3, 1), (21,
     68), (22, 70), (2, 71), (10, 10), (9, 9), (8, 8), (7, 7), (11, 21), (12, 23), (13, 36), (14,
     37), (16, 51), (20, 6), (23, 13)]
        0 11436415)
      && ((tableEntries (56 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (56 : Fin 113)) pr.2))
      && ((tableEntries (56 : Fin 113) 150).any (fun pr => 11436415 == localMaskOf (winCellList (56 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_56 :
    ∀ lam : Fin (2 ^ (winCellList (56 : Fin 113)).length),
      syndFold (winCellList (56 : Fin 113)) lam.val = 0 →
      (tableEntries (56 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (56 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_56_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (56 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_65_cert :
    (((winCellList (65 : Fin 113)).length == 24)
      && (cert1B (winCellList (65 : Fin 113))
        [(15, 49), (1, 50), (5, 64), (17, 53), (18, 60), (6, 0), (4, 4), (19, 61), (3, 1), (21,
     68), (22, 70), (2, 71), (10, 10), (9, 9), (8, 8), (7, 7), (11, 21), (12, 23), (13, 36), (14,
     37), (16, 51), (20, 6), (23, 13)]
        0 11436287)
      && ((tableEntries (65 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (65 : Fin 113)) pr.2))
      && ((tableEntries (65 : Fin 113) 150).any (fun pr => 11436287 == localMaskOf (winCellList (65 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_65 :
    ∀ lam : Fin (2 ^ (winCellList (65 : Fin 113)).length),
      syndFold (winCellList (65 : Fin 113)) lam.val = 0 →
      (tableEntries (65 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (65 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_65_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (65 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_81_cert :
    (((winCellList (81 : Fin 113)).length == 26)
      && (cert1B (winCellList (81 : Fin 113))
        [(16, 49), (1, 50), (18, 53), (20, 64), (4, 4), (5, 65), (19, 61), (3, 1), (23, 70), (10,
     10), (9, 9), (8, 8), (12, 22), (7, 21), (13, 23), (14, 36), (15, 37), (17, 51), (21, 6), (22,
     67), (2, 68), (6, 7), (11, 14), (24, 11), (25, 13)]
        0 52234367)
      && ((tableEntries (81 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (81 : Fin 113)) pr.2))
      && ((tableEntries (81 : Fin 113) 150).any (fun pr => 52234367 == localMaskOf (winCellList (81 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_81 :
    ∀ lam : Fin (2 ^ (winCellList (81 : Fin 113)).length),
      syndFold (winCellList (81 : Fin 113)) lam.val = 0 →
      (tableEntries (81 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (81 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_81_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (81 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_0_cert :
    (((winCellList (0 : Fin 113)).length == 20)
      && (cert1B (winCellList (0 : Fin 113))
        [(9, 12), (1, 11), (5, 17), (2, 3), (3, 2), (6, 6), (4, 5), (8, 9), (7, 8), (10, 0), (11,
     22), (12, 23), (13, 24), (14, 25), (15, 37), (16, 39), (17, 52), (18, 53), (19, 7)]
        0 1919)
      && ((tableEntries (0 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (0 : Fin 113)) pr.2))
      && ((tableEntries (0 : Fin 113) 150).any (fun pr => 1919 == localMaskOf (winCellList (0 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_0 :
    ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113)).length),
      syndFold (winCellList (0 : Fin 113)) lam.val = 0 →
      (tableEntries (0 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (0 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_0_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (0 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_0_c72_cert :
    (((winCellList (0 : Fin 113) ++ [72]).length == 21)
      && (cert1B (winCellList (0 : Fin 113) ++ [72])
        [(9, 12), (1, 11), (5, 17), (3, 2), (6, 6), (2, 20), (4, 5), (8, 9), (7, 8), (10, 0), (11,
     22), (12, 23), (14, 26), (13, 25), (15, 37), (16, 39), (17, 52), (18, 53), (19, 67), (20, 3)]
        0 1919)
      && ((tableEntries (0 : Fin 113) 72).any (fun pr => 0 == localMaskOf (winCellList (0 : Fin 113) ++ [72]) pr.2))
      && ((tableEntries (0 : Fin 113) 72).any (fun pr => 1919 == localMaskOf (winCellList (0 : Fin 113) ++ [72]) pr.2))) = true := by
  native_decide

theorem win_sweepE_0_c72 :
    ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113) ++ [72]).length),
      syndFold (winCellList (0 : Fin 113) ++ [72]) lam.val = 0 →
      (tableEntries (0 : Fin 113) 72).any
        (fun pr => lam.val == localMaskOf (winCellList (0 : Fin 113) ++ [72]) pr.2)
        = true := by
  have hcert := win_sweepE_0_c72_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (0 : Fin 113) ++ [72]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_0_c113_cert :
    (((winCellList (0 : Fin 113) ++ [113]).length == 21)
      && (cert1B (winCellList (0 : Fin 113) ++ [113])
        [(9, 12), (1, 11), (5, 17), (2, 3), (3, 2), (6, 6), (4, 5), (8, 9), (7, 8), (10, 0), (11,
     22), (12, 23), (13, 24), (14, 25), (15, 37), (16, 40), (17, 52), (18, 54), (19, 7), (20, 38)]
        0 1919)
      && ((tableEntries (0 : Fin 113) 113).any (fun pr => 0 == localMaskOf (winCellList (0 : Fin 113) ++ [113]) pr.2))
      && ((tableEntries (0 : Fin 113) 113).any (fun pr => 1919 == localMaskOf (winCellList (0 : Fin 113) ++ [113]) pr.2))) = true := by
  native_decide

theorem win_sweepE_0_c113 :
    ∀ lam : Fin (2 ^ (winCellList (0 : Fin 113) ++ [113]).length),
      syndFold (winCellList (0 : Fin 113) ++ [113]) lam.val = 0 →
      (tableEntries (0 : Fin 113) 113).any
        (fun pr => lam.val == localMaskOf (winCellList (0 : Fin 113) ++ [113]) pr.2)
        = true := by
  have hcert := win_sweepE_0_c113_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (0 : Fin 113) ++ [113]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepP_0_p11_81_cert :
    ((((winCellList (0 : Fin 113) ++ [11]) ++ [81]).length == 22)
      && (cert1B ((winCellList (0 : Fin 113) ++ [11]) ++ [81])
        [(9, 12), (1, 11), (10, 0), (2, 14), (5, 3), (3, 2), (6, 20), (4, 5), (8, 9), (7, 8), (11,
     22), (12, 23), (13, 24), (14, 25), (15, 37), (16, 39), (17, 52), (18, 53), (19, 67), (20,
     17), (21, 6)]
        0 1919)
      && (((tableEntries (0 : Fin 113) 11) ++ tableEntries (0 : Fin 113) 81).any (fun pr => 0 == localMaskOf ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) pr.2))
      && (((tableEntries (0 : Fin 113) 11) ++ tableEntries (0 : Fin 113) 81).any (fun pr => 1919 == localMaskOf ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) pr.2))) = true := by
  native_decide

theorem win_sweepP_0_p11_81 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [11]) ++ [81]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 11) ++ tableEntries (0 : Fin 113) 81).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [11]) ++ [81]) pr.2)
        = true := by
  have hcert := win_sweepP_0_p11_81_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ ((winCellList (0 : Fin 113) ++ [11]) ++ [81]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepP_0_p72_113_cert :
    ((((winCellList (0 : Fin 113) ++ [72]) ++ [113]).length == 22)
      && (cert1B ((winCellList (0 : Fin 113) ++ [72]) ++ [113])
        [(9, 12), (1, 11), (5, 17), (3, 2), (6, 6), (2, 20), (4, 5), (8, 9), (7, 8), (10, 0), (11,
     22), (12, 23), (14, 26), (13, 25), (15, 37), (16, 40), (17, 52), (18, 54), (19, 67), (20, 3),
     (21, 38)]
        0 1919)
      && (((tableEntries (0 : Fin 113) 72) ++ tableEntries (0 : Fin 113) 113).any (fun pr => 0 == localMaskOf ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) pr.2))
      && (((tableEntries (0 : Fin 113) 72) ++ tableEntries (0 : Fin 113) 113).any (fun pr => 1919 == localMaskOf ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) pr.2))) = true := by
  native_decide

theorem win_sweepP_0_p72_113 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [72]) ++ [113]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 72) ++ tableEntries (0 : Fin 113) 113).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [72]) ++ [113]) pr.2)
        = true := by
  have hcert := win_sweepP_0_p72_113_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ ((winCellList (0 : Fin 113) ++ [72]) ++ [113]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepP_0_p81_11_cert :
    ((((winCellList (0 : Fin 113) ++ [81]) ++ [11]).length == 22)
      && (cert1B ((winCellList (0 : Fin 113) ++ [81]) ++ [11])
        [(9, 12), (1, 11), (10, 0), (2, 14), (5, 3), (3, 2), (6, 20), (4, 5), (8, 9), (7, 8), (11,
     22), (12, 23), (13, 24), (14, 25), (15, 37), (16, 39), (17, 52), (18, 53), (19, 67), (20, 6),
     (21, 17)]
        0 1919)
      && (((tableEntries (0 : Fin 113) 81) ++ tableEntries (0 : Fin 113) 11).any (fun pr => 0 == localMaskOf ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) pr.2))
      && (((tableEntries (0 : Fin 113) 81) ++ tableEntries (0 : Fin 113) 11).any (fun pr => 1919 == localMaskOf ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) pr.2))) = true := by
  native_decide

theorem win_sweepP_0_p81_11 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [81]) ++ [11]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 81) ++ tableEntries (0 : Fin 113) 11).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [81]) ++ [11]) pr.2)
        = true := by
  have hcert := win_sweepP_0_p81_11_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ ((winCellList (0 : Fin 113) ++ [81]) ++ [11]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepP_0_p84_85_cert :
    ((((winCellList (0 : Fin 113) ++ [84]) ++ [85]).length == 22)
      && (cert1B ((winCellList (0 : Fin 113) ++ [84]) ++ [85])
        [(9, 12), (10, 29), (1, 0), (2, 14), (5, 3), (3, 2), (6, 6), (4, 5), (14, 26), (16, 40),
     (13, 39), (18, 54), (17, 53), (15, 52), (11, 37), (7, 22), (8, 8), (12, 23), (19, 7), (20,
     9), (21, 10)]
        0 1919)
      && (((tableEntries (0 : Fin 113) 84) ++ tableEntries (0 : Fin 113) 85).any (fun pr => 0 == localMaskOf ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) pr.2))
      && (((tableEntries (0 : Fin 113) 84) ++ tableEntries (0 : Fin 113) 85).any (fun pr => 1919 == localMaskOf ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) pr.2))) = true := by
  native_decide

theorem win_sweepP_0_p84_85 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [84]) ++ [85]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 84) ++ tableEntries (0 : Fin 113) 85).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [84]) ++ [85]) pr.2)
        = true := by
  have hcert := win_sweepP_0_p84_85_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ ((winCellList (0 : Fin 113) ++ [84]) ++ [85]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepP_0_p85_84_cert :
    ((((winCellList (0 : Fin 113) ++ [85]) ++ [84]).length == 22)
      && (cert1B ((winCellList (0 : Fin 113) ++ [85]) ++ [84])
        [(9, 12), (10, 29), (1, 0), (2, 14), (5, 3), (3, 2), (6, 6), (4, 5), (14, 26), (16, 40),
     (13, 39), (18, 54), (17, 53), (15, 52), (11, 37), (7, 22), (8, 8), (12, 23), (19, 7), (20,
     11), (21, 9)]
        0 1919)
      && (((tableEntries (0 : Fin 113) 85) ++ tableEntries (0 : Fin 113) 84).any (fun pr => 0 == localMaskOf ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) pr.2))
      && (((tableEntries (0 : Fin 113) 85) ++ tableEntries (0 : Fin 113) 84).any (fun pr => 1919 == localMaskOf ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) pr.2))) = true := by
  native_decide

theorem win_sweepP_0_p85_84 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [85]) ++ [84]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 85) ++ tableEntries (0 : Fin 113) 84).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [85]) ++ [84]) pr.2)
        = true := by
  have hcert := win_sweepP_0_p85_84_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ ((winCellList (0 : Fin 113) ++ [85]) ++ [84]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepP_0_p113_72_cert :
    ((((winCellList (0 : Fin 113) ++ [113]) ++ [72]).length == 22)
      && (cert1B ((winCellList (0 : Fin 113) ++ [113]) ++ [72])
        [(9, 12), (1, 11), (5, 17), (3, 2), (6, 6), (2, 20), (4, 5), (8, 9), (7, 8), (10, 0), (11,
     22), (12, 23), (14, 26), (13, 25), (15, 37), (16, 40), (17, 52), (18, 54), (19, 67), (20,
     38), (21, 3)]
        0 1919)
      && (((tableEntries (0 : Fin 113) 113) ++ tableEntries (0 : Fin 113) 72).any (fun pr => 0 == localMaskOf ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) pr.2))
      && (((tableEntries (0 : Fin 113) 113) ++ tableEntries (0 : Fin 113) 72).any (fun pr => 1919 == localMaskOf ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) pr.2))) = true := by
  native_decide

theorem win_sweepP_0_p113_72 :
    ∀ lam : Fin (2 ^ ((winCellList (0 : Fin 113) ++ [113]) ++ [72]).length),
      syndFold ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) lam.val = 0 →
      ((tableEntries (0 : Fin 113) 113) ++ tableEntries (0 : Fin 113) 72).any
        (fun pr => lam.val == localMaskOf ((winCellList (0 : Fin 113) ++ [113]) ++ [72]) pr.2)
        = true := by
  have hcert := win_sweepP_0_p113_72_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ ((winCellList (0 : Fin 113) ++ [113]) ++ [72]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_1_cert :
    (((winCellList (1 : Fin 113)).length == 23)
      && (cert1B (winCellList (1 : Fin 113))
        [(20, 64), (1, 65), (7, 4), (4, 19), (5, 5), (6, 1), (3, 16), (10, 10), (2, 11), (11, 13),
     (15, 25), (14, 24), (13, 23), (16, 37), (12, 36), (8, 21), (9, 7), (17, 38), (18, 51), (19,
     52), (21, 6), (22, 8)]
        0 5245695)
      && ((tableEntries (1 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (1 : Fin 113)) pr.2))
      && ((tableEntries (1 : Fin 113) 150).any (fun pr => 5245695 == localMaskOf (winCellList (1 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_1 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113)).length),
      syndFold (winCellList (1 : Fin 113)) lam.val = 0 →
      (tableEntries (1 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_1_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (1 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_1_c71_cert :
    (((winCellList (1 : Fin 113) ++ [71]).length == 24)
      && (cert1B (winCellList (1 : Fin 113) ++ [71])
        [(20, 64), (1, 65), (7, 4), (4, 19), (5, 5), (6, 1), (3, 16), (10, 10), (2, 11), (11, 13),
     (15, 25), (14, 24), (17, 38), (19, 53), (18, 52), (16, 51), (12, 36), (8, 21), (9, 7), (13,
     22), (21, 66), (22, 8), (23, 2)]
        0 5245695)
      && ((tableEntries (1 : Fin 113) 71).any (fun pr => 0 == localMaskOf (winCellList (1 : Fin 113) ++ [71]) pr.2))
      && ((tableEntries (1 : Fin 113) 71).any (fun pr => 5245695 == localMaskOf (winCellList (1 : Fin 113) ++ [71]) pr.2))) = true := by
  native_decide

theorem win_sweepE_1_c71 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [71]).length),
      syndFold (winCellList (1 : Fin 113) ++ [71]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 71).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [71]) pr.2)
        = true := by
  have hcert := win_sweepE_1_c71_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (1 : Fin 113) ++ [71]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_1_c73_cert :
    (((winCellList (1 : Fin 113) ++ [73]).length == 24)
      && (cert2B (winCellList (1 : Fin 113) ++ [73])
        [(11, 28), (3, 14), (4, 13), (6, 2), (5, 1), (7, 5), (10, 10), (1, 11), (20, 64), (22,
     68), (23, 4), (9, 8), (8, 7), (12, 21), (13, 22), (14, 23), (15, 24), (16, 36), (17, 38),
     (18, 51), (19, 52), (21, 6)]
        0 2 13632515 8392444)
      && ((tableEntries (1 : Fin 113) 73).any (fun pr => 0 == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2))
      && ((tableEntries (1 : Fin 113) 73).any (fun pr => 13632515 == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2))
      && ((tableEntries (1 : Fin 113) 73).any (fun pr => 8392444 == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2))
      && ((tableEntries (1 : Fin 113) 73).any (fun pr => (13632515 ^^^ 8392444) == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2))) = true := by
  native_decide

theorem win_sweepE_1_c73 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [73]).length),
      syndFold (winCellList (1 : Fin 113) ++ [73]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 73).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [73]) pr.2)
        = true := by
  have hcert := win_sweepE_1_c73_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩, htab2⟩, htab3⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (1 : Fin 113) ++ [73]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim2 hkc lam.val hlt hs with h | h | h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1
  · rw [h]
    exact htab2
  · rw [h]
    exact htab3

private theorem win_sweepE_1_c112_cert :
    (((winCellList (1 : Fin 113) ++ [112]).length == 24)
      && (cert1B (winCellList (1 : Fin 113) ++ [112])
        [(20, 64), (1, 65), (7, 4), (4, 19), (5, 5), (6, 1), (3, 16), (10, 10), (2, 11), (11, 13),
     (15, 25), (14, 24), (13, 23), (17, 39), (19, 53), (21, 67), (8, 6), (9, 7), (12, 21), (16,
     36), (18, 51), (22, 8), (23, 37)]
        0 5245695)
      && ((tableEntries (1 : Fin 113) 112).any (fun pr => 0 == localMaskOf (winCellList (1 : Fin 113) ++ [112]) pr.2))
      && ((tableEntries (1 : Fin 113) 112).any (fun pr => 5245695 == localMaskOf (winCellList (1 : Fin 113) ++ [112]) pr.2))) = true := by
  native_decide

theorem win_sweepE_1_c112 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [112]).length),
      syndFold (winCellList (1 : Fin 113) ++ [112]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 112).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [112]) pr.2)
        = true := by
  have hcert := win_sweepE_1_c112_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (1 : Fin 113) ++ [112]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_1_c140_cert :
    (((winCellList (1 : Fin 113) ++ [140]).length == 24)
      && (cert1B (winCellList (1 : Fin 113) ++ [140])
        [(20, 64), (7, 4), (4, 19), (6, 2), (3, 16), (5, 1), (10, 10), (11, 13), (2, 28), (1, 11),
     (15, 25), (14, 24), (13, 23), (16, 37), (12, 36), (8, 21), (9, 7), (17, 38), (18, 51), (19,
     52), (21, 6), (22, 8), (23, 5)]
        0 5245695)
      && ((tableEntries (1 : Fin 113) 140).any (fun pr => 0 == localMaskOf (winCellList (1 : Fin 113) ++ [140]) pr.2))
      && ((tableEntries (1 : Fin 113) 140).any (fun pr => 5245695 == localMaskOf (winCellList (1 : Fin 113) ++ [140]) pr.2))) = true := by
  native_decide

theorem win_sweepE_1_c140 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [140]).length),
      syndFold (winCellList (1 : Fin 113) ++ [140]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 140).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [140]) pr.2)
        = true := by
  have hcert := win_sweepE_1_c140_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (1 : Fin 113) ++ [140]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_1_c142_cert :
    (((winCellList (1 : Fin 113) ++ [142]).length == 24)
      && (cert1B (winCellList (1 : Fin 113) ++ [142])
        [(20, 64), (1, 65), (7, 4), (4, 19), (5, 5), (6, 1), (3, 16), (10, 10), (2, 11), (11, 13),
     (15, 25), (14, 24), (13, 23), (16, 37), (12, 36), (8, 21), (9, 22), (17, 38), (18, 51), (19,
     52), (21, 6), (22, 8), (23, 7)]
        0 5245695)
      && ((tableEntries (1 : Fin 113) 142).any (fun pr => 0 == localMaskOf (winCellList (1 : Fin 113) ++ [142]) pr.2))
      && ((tableEntries (1 : Fin 113) 142).any (fun pr => 5245695 == localMaskOf (winCellList (1 : Fin 113) ++ [142]) pr.2))) = true := by
  native_decide

theorem win_sweepE_1_c142 :
    ∀ lam : Fin (2 ^ (winCellList (1 : Fin 113) ++ [142]).length),
      syndFold (winCellList (1 : Fin 113) ++ [142]) lam.val = 0 →
      (tableEntries (1 : Fin 113) 142).any
        (fun pr => lam.val == localMaskOf (winCellList (1 : Fin 113) ++ [142]) pr.2)
        = true := by
  have hcert := win_sweepE_1_c142_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (1 : Fin 113) ++ [142]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_27_cert :
    (((winCellList (27 : Fin 113)).length == 21)
      && (cert1B (winCellList (27 : Fin 113))
        [(15, 0), (1, 61), (2, 60), (16, 3), (3, 63), (18, 6), (17, 66), (4, 65), (5, 5), (19,
     69), (6, 8), (7, 9), (8, 10), (9, 11), (10, 23), (11, 25), (12, 38), (13, 39), (14, 53), (20,
     12)]
        0 1540671)
      && ((tableEntries (27 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (27 : Fin 113)) pr.2))
      && ((tableEntries (27 : Fin 113) 150).any (fun pr => 1540671 == localMaskOf (winCellList (27 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_27 :
    ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113)).length),
      syndFold (winCellList (27 : Fin 113)) lam.val = 0 →
      (tableEntries (27 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (27 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_27_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (27 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_27_c58_cert :
    (((winCellList (27 : Fin 113) ++ [58]).length == 22)
      && (cert1B (winCellList (27 : Fin 113) ++ [58])
        [(15, 0), (1, 61), (2, 60), (16, 3), (3, 63), (18, 6), (17, 66), (4, 65), (5, 5), (19,
     69), (6, 8), (7, 9), (10, 23), (12, 38), (13, 39), (11, 40), (8, 25), (9, 11), (14, 53), (20,
     12), (21, 10)]
        0 1540671)
      && ((tableEntries (27 : Fin 113) 58).any (fun pr => 0 == localMaskOf (winCellList (27 : Fin 113) ++ [58]) pr.2))
      && ((tableEntries (27 : Fin 113) 58).any (fun pr => 1540671 == localMaskOf (winCellList (27 : Fin 113) ++ [58]) pr.2))) = true := by
  native_decide

theorem win_sweepE_27_c58 :
    ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113) ++ [58]).length),
      syndFold (winCellList (27 : Fin 113) ++ [58]) lam.val = 0 →
      (tableEntries (27 : Fin 113) 58).any
        (fun pr => lam.val == localMaskOf (winCellList (27 : Fin 113) ++ [58]) pr.2)
        = true := by
  have hcert := win_sweepE_27_c58_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (27 : Fin 113) ++ [58]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_27_c99_cert :
    (((winCellList (27 : Fin 113) ++ [99]).length == 22)
      && (cert1B (winCellList (27 : Fin 113) ++ [99])
        [(15, 0), (1, 61), (2, 60), (16, 3), (3, 63), (18, 6), (17, 66), (4, 65), (5, 5), (19,
     69), (6, 8), (7, 9), (8, 10), (9, 11), (10, 23), (11, 26), (12, 38), (13, 40), (14, 53), (20,
     12), (21, 24)]
        0 1540671)
      && ((tableEntries (27 : Fin 113) 99).any (fun pr => 0 == localMaskOf (winCellList (27 : Fin 113) ++ [99]) pr.2))
      && ((tableEntries (27 : Fin 113) 99).any (fun pr => 1540671 == localMaskOf (winCellList (27 : Fin 113) ++ [99]) pr.2))) = true := by
  native_decide

theorem win_sweepE_27_c99 :
    ∀ lam : Fin (2 ^ (winCellList (27 : Fin 113) ++ [99]).length),
      syndFold (winCellList (27 : Fin 113) ++ [99]) lam.val = 0 →
      (tableEntries (27 : Fin 113) 99).any
        (fun pr => lam.val == localMaskOf (winCellList (27 : Fin 113) ++ [99]) pr.2)
        = true := by
  have hcert := win_sweepE_27_c99_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (27 : Fin 113) ++ [99]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweep0_28_cert :
    (((winCellList (28 : Fin 113)).length == 23)
      && (cert1B (winCellList (28 : Fin 113))
        [(10, 0), (5, 29), (21, 12), (20, 72), (1, 71), (16, 2), (2, 63), (3, 62), (17, 5), (4,
     65), (9, 11), (8, 10), (7, 9), (11, 23), (6, 22), (12, 24), (13, 37), (14, 38), (15, 52),
     (18, 7), (19, 8), (22, 14)]
        0 7537727)
      && ((tableEntries (28 : Fin 113) 150).any (fun pr => 0 == localMaskOf (winCellList (28 : Fin 113)) pr.2))
      && ((tableEntries (28 : Fin 113) 150).any (fun pr => 7537727 == localMaskOf (winCellList (28 : Fin 113)) pr.2))) = true := by
  native_decide

theorem win_sweep0_28 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113)).length),
      syndFold (winCellList (28 : Fin 113)) lam.val = 0 →
      (tableEntries (28 : Fin 113) 150).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113)) pr.2)
        = true := by
  have hcert := win_sweep0_28_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (28 : Fin 113)).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_28_c47_cert :
    (((winCellList (28 : Fin 113) ++ [47]).length == 24)
      && (cert2B (winCellList (28 : Fin 113) ++ [47])
        [(4, 69), (10, 0), (5, 29), (17, 65), (2, 5), (3, 66), (16, 62), (1, 2), (20, 71), (9,
     11), (8, 10), (7, 9), (6, 8), (11, 22), (12, 24), (13, 37), (14, 38), (15, 52), (18, 7), (21,
     12), (22, 60), (23, 14)]
        0 19 7537727 14352414)
      && ((tableEntries (28 : Fin 113) 47).any (fun pr => 0 == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2))
      && ((tableEntries (28 : Fin 113) 47).any (fun pr => 7537727 == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2))
      && ((tableEntries (28 : Fin 113) 47).any (fun pr => 14352414 == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2))
      && ((tableEntries (28 : Fin 113) 47).any (fun pr => (7537727 ^^^ 14352414) == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2))) = true := by
  native_decide

theorem win_sweepE_28_c47 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [47]).length),
      syndFold (winCellList (28 : Fin 113) ++ [47]) lam.val = 0 →
      (tableEntries (28 : Fin 113) 47).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [47]) pr.2)
        = true := by
  have hcert := win_sweepE_28_c47_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩, htab2⟩, htab3⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (28 : Fin 113) ++ [47]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim2 hkc lam.val hlt hs with h | h | h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1
  · rw [h]
    exact htab2
  · rw [h]
    exact htab3

private theorem win_sweepE_28_c57_cert :
    (((winCellList (28 : Fin 113) ++ [57]).length == 24)
      && (cert1B (winCellList (28 : Fin 113) ++ [57])
        [(10, 0), (5, 29), (21, 12), (20, 72), (1, 71), (16, 2), (3, 62), (17, 66), (2, 5), (4,
     65), (9, 11), (8, 10), (12, 24), (14, 39), (13, 38), (11, 37), (6, 22), (7, 23), (15, 52),
     (18, 7), (19, 8), (22, 14), (23, 9)]
        0 7537727)
      && ((tableEntries (28 : Fin 113) 57).any (fun pr => 0 == localMaskOf (winCellList (28 : Fin 113) ++ [57]) pr.2))
      && ((tableEntries (28 : Fin 113) 57).any (fun pr => 7537727 == localMaskOf (winCellList (28 : Fin 113) ++ [57]) pr.2))) = true := by
  native_decide

theorem win_sweepE_28_c57 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [57]).length),
      syndFold (winCellList (28 : Fin 113) ++ [57]) lam.val = 0 →
      (tableEntries (28 : Fin 113) 57).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [57]) pr.2)
        = true := by
  have hcert := win_sweepE_28_c57_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (28 : Fin 113) ++ [57]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

private theorem win_sweepE_28_c98_cert :
    (((winCellList (28 : Fin 113) ++ [98]).length == 24)
      && (cert1B (winCellList (28 : Fin 113) ++ [98])
        [(10, 0), (5, 29), (21, 12), (20, 72), (1, 71), (16, 2), (2, 63), (3, 62), (17, 5), (4,
     65), (9, 11), (8, 10), (7, 9), (12, 25), (14, 39), (15, 53), (13, 52), (11, 37), (6, 22),
     (18, 7), (19, 8), (22, 14), (23, 23)]
        0 7537727)
      && ((tableEntries (28 : Fin 113) 98).any (fun pr => 0 == localMaskOf (winCellList (28 : Fin 113) ++ [98]) pr.2))
      && ((tableEntries (28 : Fin 113) 98).any (fun pr => 7537727 == localMaskOf (winCellList (28 : Fin 113) ++ [98]) pr.2))) = true := by
  native_decide

theorem win_sweepE_28_c98 :
    ∀ lam : Fin (2 ^ (winCellList (28 : Fin 113) ++ [98]).length),
      syndFold (winCellList (28 : Fin 113) ++ [98]) lam.val = 0 →
      (tableEntries (28 : Fin 113) 98).any
        (fun pr => lam.val == localMaskOf (winCellList (28 : Fin 113) ++ [98]) pr.2)
        = true := by
  have hcert := win_sweepE_28_c98_cert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hlen, hkc⟩, htab0⟩, htab1⟩ := hcert
  rw [hlen]
  intro lam hs
  have hlt : lam.val < 2 ^ (winCellList (28 : Fin 113) ++ [98]).length := by
    rw [hlen]
    exact lam.isLt
  rcases kernel_classify_dim1 hkc lam.val hlt hs with h | h
  · rw [h]
    exact htab0
  · rw [h]
    exact htab1

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

/-! ## Assembly support: class-shape certificates + sweep dispatch -/

theorem kind_cases : ∀ i : Fin 113,
    KIND.getD i.val 0 = 0 ∨ KIND.getD i.val 0 = 1 := by
  native_decide

theorem win_t_cases : ∀ i : Fin 113, KIND.getD i.val 0 = 1 →
    tOf i = 1 ∨ tOf i = 2 ∨ tOf i = 3 := by
  native_decide

theorem s_weight_certs : ∀ i : Fin 113, KIND.getD i.val 0 = 0 →
    (Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 (sF0Chain i) j ≠ 0).card
      = BW.getD i.val 0 := by
  native_decide

theorem win_sweep0_dispatch (i : Fin 113) (hk : KIND.getD i.val 0 = 1) :
    ∀ lam : Fin (2 ^ (winCellList i).length),
      syndFold (winCellList i) lam.val = 0 →
      (tableEntries i 150).any
        (fun pr => lam.val == localMaskOf (winCellList i) pr.2) = true := by
  fin_cases i
  · exact win_sweep0_0
  · exact win_sweep0_1
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_4
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_24
  · exact win_sweep0_25
  · exact win_sweep0_26
  · exact win_sweep0_27
  · exact win_sweep0_28
  · exact win_sweep0_29
  · exact win_sweep0_30
  · exact absurd hk (by decide)
  · exact win_sweep0_32
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_37
  · exact win_sweep0_38
  · exact win_sweep0_39
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_49
  · exact win_sweep0_50
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_56
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_65
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact win_sweep0_81
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem win_sweepE_dispatch (i : Fin 113) (hk : KIND.getD i.val 0 = 1) (ht : 2 ≤ tOf i) :
    ∀ e : G150 × Fin 2, winMem i e = false →
      survivorB i (cellIdx e) = true →
      ∀ lam : Fin (2 ^ (winCellList i ++ [cellIdx e]).length),
        syndFold (winCellList i ++ [cellIdx e]) lam.val = 0 →
        (tableEntries i (cellIdx e)).any (fun pr =>
          lam.val == localMaskOf (winCellList i ++ [cellIdx e]) pr.2)
          = true := by
  fin_cases i
  · exact win_sweepE_0
  · exact win_sweepE_1
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact win_sweepE_27
  · exact win_sweepE_28
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem win_sweepP_dispatch (i : Fin 113) (hk : KIND.getD i.val 0 = 1) (ht : tOf i = 3) :
    ∀ e₁ e₂ : G150 × Fin 2, winMem i e₁ = false →
      winMem i e₂ = false → e₁ ≠ e₂ →
      pairSurvivorB i (cellIdx e₁) (cellIdx e₂) = true →
      ∀ lam : Fin (2 ^ ((winCellList i ++ [cellIdx e₁]) ++ [cellIdx e₂]).length),
        syndFold ((winCellList i ++ [cellIdx e₁]) ++ [cellIdx e₂]) lam.val = 0 →
        ((tableEntries i (cellIdx e₁)) ++ tableEntries i (cellIdx e₂)).any
          (fun pr => lam.val ==
            localMaskOf ((winCellList i ++ [cellIdx e₁]) ++ [cellIdx e₂])
              pr.2) = true := by
  fin_cases i
  · exact win_sweepP_0
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd ht (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)


end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

/-
# The dangerous sector of the [[300,8,16]] cover: `≥ 16` at nonzero slice

`dangerousFloorNZ_of_lightClassification` — every nontrivial cover cycle
whose pushforward is a nonzero base boundary has weight ≥ 16, given the
logical base floor and the light-boundary classification.

Dispatch: if `|p(v)| ≥ 16` the slice inequality closes directly.
Otherwise parity forces `|p(v)| ≤ 14`, the classification pins `p(v)` to
a base translate of one of the 113 class representatives, and
`weight_floor_translate1_reduce` walks the translation orbit down to the
tabulated representative, where the class splits by `KIND`:

* the 94 **small** classes have seam-good preimages (`sF0Chain`,
  certified by `s_translate_certs`/`s_seam_certs`) and fall to the
  single-shape rung `dangerous_bound_of_single_shape_of_logicalFloor`;
* the 19 **near-kernel window** classes have min-poke preimages
  (`winF0Chain`, certified by `win_f0_certs`) and fall to the
  generalized window rung `dangerous_bound_of_window_general`, whose
  window hypothesis is discharged by `window_sound_t1/t2/t3` over the
  pivot-certificate sweeps (`SweepWin.lean`), bridged through
  `win_mem_certs`.
-/

import QEC.Stabilizer.Framework.Homological.BBCoverTranslate
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SweepWin

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

-- Defeq checks through `coverData`'s complex projections unfold deep
-- `Prod`/`ZMod` instance chains (same as the other instance files).
set_option maxRecDepth 4096

/-- The dangerous-floor clause at a small class representative's
tabulated seam-good boundary. -/
theorem class_floor_small (hbase : coverData.LogicalFloor 8) (i : Fin 113)
    (hk : KIND.getD i.val 0 = 0) :
    ∀ v : G300 × Fin 2 → ZMod 2, v ∈ coverData.coverComplex.cycles →
      v ∉ coverData.coverComplex.boundaries →
      coverData.push1 v = bbBoundary2Fn a150 b150 (sF0Chain i) →
      2 * 8 ≤ coverData.coverComplex.chainWeight v := by
  intro v hv hnb hb
  refine coverData.dangerous_bound_of_single_shape_of_logicalFloor hbase
    (class_t_certs i).1 (sF0Chain i) ?_ (s_seam_certs i hk) hv hnb hb
  rw [coverData.baseComplex_chainWeight_eq]
  change (Finset.univ.filter fun j : G150 × Fin 2 =>
    bbBoundary2Fn a150 b150 (sF0Chain i) j ≠ 0).card + 2 * tOf i = 2 * 8
  rw [s_weight_certs i hk]
  have h2 := (class_t_certs i).2
  omega

/-- The dangerous-floor clause at a window class representative's
tabulated min-poke boundary. -/
theorem class_floor_window (i : Fin 113) (hk : KIND.getD i.val 0 = 1) :
    ∀ v : G300 × Fin 2 → ZMod 2, v ∈ coverData.coverComplex.cycles →
      v ∉ coverData.coverComplex.boundaries →
      coverData.push1 v = bbBoundary2Fn a150 b150 (winF0Chain i) →
      2 * 8 ≤ coverData.coverComplex.chainWeight v := by
  classical
  intro v hv hnb hb
  refine coverData.dangerous_bound_of_window_general
    (class_t_certs i).1 (winF0Chain i) ?_ ?_ hv hnb hb
  · -- the tabulated boundary's weight makes up the deficit exactly
    rw [coverData.baseComplex_chainWeight_eq]
    change (Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 (winF0Chain i) j ≠ 0).card + 2 * tOf i
        = 2 * 8
    rw [win_f0_certs i hk, rep_weight_certs i]
    have h2 := (class_t_certs i).2
    omega
  · -- window hypothesis: near-window cycles are boundaries
    intro u hcyc hcard
    have hcyc' : bbBoundary1Fn a150 b150 u = 0 := hcyc
    -- bridge the rung's filter to the tabulated window membership
    have hEq : (Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem i j = true)
        = (Finset.univ.filter fun j : G150 × Fin 2 => u j ≠ 0 ∧
          ¬ (bbBoundary2Fn coverData.Ab coverData.Bb (winF0Chain i) j ≠ 0
            ∨ coverData.sheet0 (coverData.liftStab (winF0Chain i)) j
              ≠ 0)) := by
      apply Finset.filter_congr
      intro j _
      exact and_congr_right fun _ => not_congr (win_mem_certs i hk j)
    have hcard' : (Finset.univ.filter fun j : G150 × Fin 2 =>
        u j ≠ 0 ∧ ¬ winMem i j = true).card ≤ tOf i - 1 := by
      rw [hEq]
      exact hcard
    have hbd : u ∈ base150Complex.boundaries := by
      rcases win_t_cases i hk with ht | ht | ht
      · -- t = 1: no support outside the window
        rw [ht] at hcard'
        have hsupp : ∀ j : G150 × Fin 2, u j ≠ 0 → winMem i j = true := by
          intro j hj
          by_contra hnm
          have hmem : j ∈ Finset.univ.filter (fun j : G150 × Fin 2 =>
              u j ≠ 0 ∧ ¬ winMem i j = true) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hnm⟩
          have hcz : (Finset.univ.filter fun j : G150 × Fin 2 =>
              u j ≠ 0 ∧ ¬ winMem i j = true).card = 0 := by omega
          rw [Finset.card_eq_zero.mp hcz] at hmem
          exact Finset.notMem_empty j hmem
        exact window_sound_t1 i hk (win_sweep0_dispatch i hk) hcyc' hsupp
      · -- t = 2: at most one cell outside the window
        rw [ht] at hcard'
        exact window_sound_t2 i hk (win_sweep0_dispatch i hk)
          (win_sweepE_dispatch i hk (by omega)) hcyc' (by omega)
      · -- t = 3: at most two cells outside the window
        rw [ht] at hcard'
        exact window_sound_t3 i hk (win_sweep0_dispatch i hk)
          (win_sweepE_dispatch i hk (by omega))
          (win_sweepP_dispatch i hk ht) hcyc' (by omega)
    exact hbd

/-- **The dangerous floor at nonzero slice, from the classification.**
Every nontrivial cover cycle whose pushforward is a nonzero base
boundary has weight ≥ 16, given the logical base floor (`d(base) ≥ 8`)
and the light-boundary classification. -/
theorem dangerousFloorNZ_of_lightClassification
    (hbase : coverData.LogicalFloor 8) (hcls : LightClassification) :
    coverData.DangerousFloorNZ 16 := by
  intro v hv hnb hbmem hbne
  -- destructure the boundary membership with `f` born over the concrete
  -- group type (the submodule's own carrier is only defeq to it)
  obtain ⟨f, hf'⟩ : ∃ f : G150 → ZMod 2,
      bbBoundary2Fn a150 b150 f = coverData.push1 v := by
    obtain ⟨fraw, hfraw⟩ := hbmem
    exact ⟨fraw, hfraw⟩
  by_cases hw : 16 ≤ coverData.baseComplex.chainWeight (coverData.push1 v)
  · exact le_trans hw (coverData.chainWeight_push_le v)
  · push_neg at hw
    have hne : bbBoundary2Fn a150 b150 f ≠ 0 := by
      rw [hf']
      exact hbne
    have hle15 : (Finset.univ.filter fun j : G150 × Fin 2 =>
        bbBoundary2Fn a150 b150 f j ≠ 0).card ≤ 15 := by
      have heq : (Finset.univ.filter fun j : G150 × Fin 2 =>
          bbBoundary2Fn a150 b150 f j ≠ 0).card
          = coverData.baseComplex.chainWeight (coverData.push1 v) := by
        rw [coverData.baseComplex_chainWeight_eq, hf']
      omega
    have hle14 := boundary_chainWeight_le_14 f hle15
    obtain ⟨i, c, heq⟩ := hcls f hne hle14
    have hpv : coverData.push1 v = translate1 c (repChain i) := by
      rw [← hf', heq]
    have h16 : 2 * 8 ≤ coverData.coverComplex.chainWeight v := by
      rcases kind_cases i with hk | hk
      · -- small class: walk the orbit to the tabulated seam-good translate
        have hrep' : repChain i = translate1 (-(sShiftEl i))
            (bbBoundary2Fn a150 b150 (sF0Chain i)) := by
          rw [s_translate_certs i hk, translate1_translate1,
            neg_add_cancel, translate1_zero]
        have hpush : coverData.push1 v = translate1 (c + -(sShiftEl i))
            (bbBoundary2Fn a150 b150 (sF0Chain i)) := by
          rw [hpv, hrep', translate1_translate1]
        exact coverData.weight_floor_translate1_reduce
          (proj_lift (c + -(sShiftEl i)))
          (class_floor_small hbase i hk) v hv hnb hpush
      · -- window class: the tabulated preimage hits the rep itself
        have hpush : coverData.push1 v = translate1 c
            (bbBoundary2Fn a150 b150 (winF0Chain i)) := by
          rw [hpv, win_f0_certs i hk]
        exact coverData.weight_floor_translate1_reduce (proj_lift c)
          (class_floor_window i hk) v hv hnb hpush
    omega

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

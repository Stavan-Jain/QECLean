import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.MiddleFloorData
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Fibers
import QEC.Stabilizer.Framework.Homological.Certificate.MaskDual

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData MiddleFloorData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The prepacked E columns are the actual carry columns. -/
theorem middleEmpty_eColumn : ∀ q : Fin 90,
    reconX bottomEColumns (2 ^ q.val) = eColumn q := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each small logical-shadow certificate uses its actual right-hand side and overflow budget. -/
theorem middleEmpty_rhsCap : ∀ i : Fin 38,
    reconX bottomRColumns (emptyBeta i) = emptyRhs i ∧
      (10 - bitCount 90 (emptyBeta i)) / 2 = emptyCap i ∧
      emptyCap i ≤ 1 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every listed dual annihilates the columns on its shadow support. -/
theorem middleEmpty_on : ∀ (i : Fin 38) (j : Fin 6) (q : Fin 90),
    (emptyBeta i).testBit q.val = true →
      parityFold 7 (emptyLambda (6 * i.val + j.val) &&& eColumn q) = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each logical-shadow right-hand side is detected by one listed dual. -/
theorem middleEmpty_zero : ∀ i : Fin 38,
    ∃ j : Fin 6, parityFold 7
      (emptyLambda (6 * i.val + j.val) &&& emptyRhs i) = 1 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- For the two overflow-one cases, every possible extra bit is excluded by a listed dual. -/
theorem middleEmpty_single : ∀ i : Fin 38, emptyCap i = 1 →
    ∀ q : Fin 90, (emptyBeta i).testBit q.val = false →
      ∃ j : Fin 6,
        parityFold 7 (emptyLambda (6 * i.val + j.val) &&& emptyRhs i) = 1 ∧
          parityFold 7 (emptyLambda (6 * i.val + j.val) &&& eColumn q) = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A middle cycle of weight at most ten cannot have one of the small logical base shadows. -/
theorem middle_empty_shadow_impossible {v : MiddleGroup × Fin 2 → ZMod 2}
    (hv : v ∈ middleComplex.cycles) (hw : middleComplex.chainWeight v ≤ 10)
    (i : Fin 38) (hshadow : maskOf baseQubitEnum (baseCover.push1 v) = emptyBeta i) : False := by
  obtain ⟨hrhs, hcap, hcaple⟩ := middleEmpty_rhsCap i
  have hne := no_recon_solution_small_cap (n := 90) (k := 7) bottomEColumns
    (emptyRhs i) (emptyBeta i) (emptyCap i)
    (fun j : Fin 6 => emptyLambda (6 * i.val + j.val)) hcaple
    (by intro j q hq; rw [middleEmpty_eColumn]; exact middleEmpty_on i j q hq)
    (middleEmpty_zero i)
    (by intro hc q hq; simpa only [middleEmpty_eColumn] using middleEmpty_single i hc q hq)
    (maskOf baseQubitEnum (baseCover.sheet0 v)) (maskOf_lt _ _)
    (by rw [← hshadow]; exact maskOf_lt _ _)
    (by
      have ho := baseCover.mask_overflow_le baseQubitEnum v hw
      rwa [hshadow, hcap] at ho)
  apply hne
  rw [bottom_fiber_equation hv, hshadow, hrhs]

end Quantum.Stabilizer.Homological.BB.Bravyi360

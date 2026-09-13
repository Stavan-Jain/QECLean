import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Code
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.LowerBound
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.DistanceGrowth

/-!
# A BB family with unbounded and strictly increasing figure of merit

For every positive mathematical index `s`, the checks are
`1+x+x^(2^s)` and `1+y+y^(2^s)` on a square torus of side `4^s-1`.
The quantum distance equals the minimum distance of its explicit classical
recurrence space. The proved lower bound, without any assumed closed distance
formula, makes `k*d^2/n` unbounded and strictly increasing on `s=16*4^t`.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

/-- The attained seed minimum obeys the unconditional Pascal-averaging bound. -/
theorem seedDistance_lower (s : ℕ) :
    3 ^ (s + 1) ≤ 2 * (s + 1) * seedDistance s := by
  obtain ⟨c, hc, hc0, hw⟩ := exists_seedDistance_word s
  rw [← hw]
  exact seedSpace_weight_lower s c hc hc0

/-- Classical distance at the positive mathematical index; zero is unused by
the family theorems. -/
noncomputable def distanceAt (s : ℕ) : ℕ := seedDistance (s - 1)

/-- The physical-length upper bound in positive-index notation. -/
theorem distanceAt_le_period (s : ℕ) (hs : 0 < s) : distanceAt s ≤ period s := by
  have h := seedDistance_le_period (s - 1)
  simpa only [Nat.sub_add_cancel hs, distanceAt] using h

/-- The unconditional distance lower bound in positive-index notation. -/
theorem distanceAt_lower (s : ℕ) (hs : 0 < s) :
    3 ^ s ≤ 2 * s * distanceAt s := by
  have h := seedDistance_lower (s - 1)
  simpa only [Nat.sub_add_cancel hs, distanceAt] using h

/-- The selected BB code, with all three parameters stated explicitly. -/
noncomputable def growingCode (t : ℕ) :
    Quantum.StabilizerGroup.StabilizerCodeWithDistance
      (2 * period (growthIndex t) ^ 2)
      (2 * width (growthIndex t) ^ 2) (distanceAt (growthIndex t)) := by
  have hs : 0 < growthIndex t := lt_of_lt_of_le (by decide : 0 < 16)
    (sixteen_le_growthIndex t)
  simpa only [Nat.sub_add_cancel hs, distanceAt] using
    stabilizerCodeWithDistance (growthIndex t - 1)

/-- The actual figure of merit of the selected codes, canceling the common
factor two in their physical and logical dimensions. -/
noncomputable def growingEfficiency (t : ℕ) : ℚ :=
  efficiencyRatio (growthIndex t) (distanceAt (growthIndex t))

/-- The canceled ratio is exactly `k*d^2/n` for the packaged code parameters. -/
theorem growingEfficiency_eq_kd2_div_n (t : ℕ) :
    growingEfficiency t =
      ((2 * width (growthIndex t) ^ 2 : ℕ) : ℚ) *
        (distanceAt (growthIndex t) : ℚ) ^ 2 /
          ((2 * period (growthIndex t) ^ 2 : ℕ) : ℚ) := by
  unfold growingEfficiency efficiencyRatio
  push_cast
  ring

/-- The actual figures of merit are strictly increasing with the family index. -/
theorem growingEfficiency_strictMono : StrictMono growingEfficiency :=
  efficiencyRatio_strictMono_growthIndex distanceAt distanceAt_le_period distanceAt_lower

/-- Every integer efficiency threshold is exceeded at an explicitly given
family index. This establishes unbounded actual `k*d^2/n`. -/
theorem growingEfficiency_unbounded (bound : ℕ) :
    (bound : ℚ) < growingEfficiency (bound + 1) :=
  efficiencyRatio_unbounded_growthIndex distanceAt distanceAt_lower bound

end Quantum.Stabilizer.Homological.BB.Fractal

import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Polynomial

/-!
# Increasing distance efficiency for the fractal BB family

The only distance inputs are the proved fractal floor `3^s ≤ 2*s*d_s` and
the elementary length bound `d_s ≤ period s`. Integer cross multiplication
shows strict improvement on the explicit subsequence `s = 16*4^t`.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

/-- The exponential term dominates the linear loss in the averaging theorem. -/
lemma eight_mul_le_two_pow {s : ℕ} (hs : 16 ≤ s) : 8 * s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    omega

/-- At four times the index, the proved distance floor exceeds the product
of the old and new recurrence widths. -/
theorem distance_four_mul_gt_width_product {s d : ℕ} (hs : 16 ≤ s)
    (hd : 3 ^ (4 * s) ≤ 2 * (4 * s) * d) :
    width (4 * s) * width s < d := by
  have h8 := eight_mul_le_two_pow hs
  have hpower : (64 : ℕ) ^ s < 81 ^ s :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  have htwo : 2 ^ s * (width (4 * s) * width s) = 64 ^ s := by
    unfold width
    rw [← mul_assoc, ← pow_add, ← pow_add]
    rw [show s + 4 * s + s = 6 * s by omega, pow_mul]
    norm_num
  have hthree : (3 : ℕ) ^ (4 * s) = 81 ^ s := by
    rw [pow_mul]
    norm_num
  have hbudget : 2 * (4 * s) * (width (4 * s) * width s) < 3 ^ (4 * s) := by
    calc
      2 * (4 * s) * (width (4 * s) * width s) =
          (8 * s) * (width (4 * s) * width s) := by ring
      _ ≤ 2 ^ s * (width (4 * s) * width s) := Nat.mul_le_mul_right _ h8
      _ = 64 ^ s := htwo
      _ < 81 ^ s := hpower
      _ = 3 ^ (4 * s) := hthree.symm
  nlinarith

/-- The period is strictly below the square of its recurrence width. -/
lemma period_lt_width_sq (s : ℕ) : period s < width s ^ 2 := by
  unfold period
  exact Nat.sub_lt (by have := width_pos s; positivity) (by decide)

/-- The new normalized squared distance already exceeds the old width squared. -/
theorem distance_four_mul_cross_gt {s d : ℕ} (hs : 16 ≤ s)
    (hd : 3 ^ (4 * s) ≤ 2 * (4 * s) * d) :
    width s ^ 2 * period (4 * s) ^ 2 < width (4 * s) ^ 2 * d ^ 2 := by
  have hdist := distance_four_mul_gt_width_product hs hd
  have hlinear : width s * period (4 * s) < width (4 * s) * d := by
    calc
      width s * period (4 * s) < width s * (width (4 * s) ^ 2) :=
        Nat.mul_lt_mul_of_pos_left (period_lt_width_sq _) (width_pos s)
      _ = width (4 * s) * (width (4 * s) * width s) := by ring
      _ < width (4 * s) * d := Nat.mul_lt_mul_of_pos_left hdist (width_pos _)
  simpa only [mul_pow] using Nat.pow_lt_pow_left hlinear (by decide : 2 ≠ 0)

/-- Integer cross multiplication proves strict improvement of `k*d^2/n` at
four times the index using only the distance floor and the old length upper bound. -/
theorem efficiency_cross_increases_four_mul {s d e : ℕ} (hs : 16 ≤ s)
    (hd : d ≤ period s) (he : 3 ^ (4 * s) ≤ 2 * (4 * s) * e) :
    (width s ^ 2 * d ^ 2) * period (4 * s) ^ 2 <
      (width (4 * s) ^ 2 * e ^ 2) * period s ^ 2 := by
  have hs0 : 0 < s := by omega
  have hn : 0 < period s := by have := three_le_period hs0; omega
  have hsq : d ^ 2 ≤ period s ^ 2 := Nat.pow_le_pow_left hd 2
  calc
    (width s ^ 2 * d ^ 2) * period (4 * s) ^ 2 ≤
        (width s ^ 2 * period s ^ 2) * period (4 * s) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq)
    _ = (width s ^ 2 * period (4 * s) ^ 2) * period s ^ 2 := by ring
    _ < (width (4 * s) ^ 2 * e ^ 2) * period s ^ 2 :=
      Nat.mul_lt_mul_of_pos_right (distance_four_mul_cross_gt hs he) (by positivity)

/-- A concrete family of positive indices on which the actual figure of merit
strictly improves even without an exact formula for the classical distance. -/
def growthIndex (t : ℕ) : ℕ := 16 * 4 ^ t

/-- Every selected index lies in the proved growth regime. -/
lemma sixteen_le_growthIndex (t : ℕ) : 16 ≤ growthIndex t := by
  have h : 0 < (4 : ℕ) ^ t := by positivity
  unfold growthIndex
  omega

/-- Consecutive selected indices differ by a factor of four. -/
lemma growthIndex_succ (t : ℕ) : growthIndex (t + 1) = 4 * growthIndex t := by
  simp only [growthIndex, pow_succ]
  ring

/-- A distance sequence satisfying the proved lower bound and its physical
length bound has strictly improving integer cross products on `growthIndex`. -/
theorem efficiency_cross_increases_growthIndex (d : ℕ → ℕ)
    (hupper : ∀ s, 0 < s → d s ≤ period s)
    (hlower : ∀ s, 0 < s → 3 ^ s ≤ 2 * s * d s) (t : ℕ) :
    (width (growthIndex t) ^ 2 * d (growthIndex t) ^ 2) *
        period (growthIndex (t + 1)) ^ 2 <
      (width (growthIndex (t + 1)) ^ 2 * d (growthIndex (t + 1)) ^ 2) *
        period (growthIndex t) ^ 2 := by
  have hs := sixteen_le_growthIndex t
  rw [growthIndex_succ]
  exact efficiency_cross_increases_four_mul hs
    (hupper _ (by omega)) (hlower _ (by omega))

/-- The selected index exceeds its sequence position. -/
lemma index_lt_growthIndex (t : ℕ) : t < growthIndex t := by
  have h : t < (4 : ℕ) ^ t := Nat.lt_pow_self (by decide)
  unfold growthIndex
  omega

/-- The next selected code exceeds any prescribed integer efficiency bound.
The witness is explicit: the selected position is one more than that bound. -/
theorem efficiency_cross_exceeds_bound (d : ℕ → ℕ)
    (hlower : ∀ s, 0 < s → 3 ^ s ≤ 2 * s * d s) (bound : ℕ) :
    bound * period (growthIndex (bound + 1)) ^ 2 <
      width (growthIndex (bound + 1)) ^ 2 * d (growthIndex (bound + 1)) ^ 2 := by
  have hs := sixteen_le_growthIndex bound
  have hindex := index_lt_growthIndex bound
  have hwidth : growthIndex bound < width (growthIndex bound) := Nat.lt_two_pow_self
  have hsmall : bound ≤ width (growthIndex bound) ^ 2 := by nlinarith
  rw [growthIndex_succ]
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hsmall)
    (distance_four_mul_cross_gt hs (hlower _ (by omega)))

/-- The figure of merit `k*d^2/n`, with its common factor two canceled. -/
def efficiencyRatio (s d : ℕ) : ℚ :=
  ((width s ^ 2 * d ^ 2 : ℕ) : ℚ) / ((period s ^ 2 : ℕ) : ℚ)

/-- The actual rational figure of merit is strictly increasing on the explicit
subsequence whenever the sequence satisfies the proved distance bounds. -/
theorem efficiencyRatio_strictMono_growthIndex (d : ℕ → ℕ)
    (hupper : ∀ s, 0 < s → d s ≤ period s)
    (hlower : ∀ s, 0 < s → 3 ^ s ≤ 2 * s * d s) :
    StrictMono (fun t => efficiencyRatio (growthIndex t) (d (growthIndex t))) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hperiod (i : ℕ) : 0 < period (growthIndex i) := by
    have hi := sixteen_le_growthIndex i
    have := three_le_period (show 0 < growthIndex i by omega)
    omega
  unfold efficiencyRatio
  apply (div_lt_div_iff₀ (by exact_mod_cast pow_pos (hperiod t) 2)
    (by exact_mod_cast pow_pos (hperiod (t + 1)) 2)).2
  exact_mod_cast efficiency_cross_increases_growthIndex d hupper hlower t

/-- The same explicit subsequence has unbounded actual figure of merit, stated
against every natural threshold without an asymptotic or topological dependency. -/
theorem efficiencyRatio_unbounded_growthIndex (d : ℕ → ℕ)
    (hlower : ∀ s, 0 < s → 3 ^ s ≤ 2 * s * d s) (bound : ℕ) :
    (bound : ℚ) <
      efficiencyRatio (growthIndex (bound + 1)) (d (growthIndex (bound + 1))) := by
  have hi := sixteen_le_growthIndex (bound + 1)
  have hn : 0 < period (growthIndex (bound + 1)) := by
    have := three_le_period (show 0 < growthIndex (bound + 1) by omega)
    omega
  unfold efficiencyRatio
  apply (lt_div_iff₀ (by exact_mod_cast pow_pos hn 2)).2
  exact_mod_cast efficiency_cross_exceeds_bound d hlower bound

end Quantum.Stabilizer.Homological.BB.Fractal

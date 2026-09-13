import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Recurrence
import Mathlib.InformationTheory.Hamming

/-!
# The exact classical distance of each fractal seed

The distance is the least weight of a nonzero word in the concrete recurrence
space. Its minimum is attained. This definition makes no conjecture about a
closed formula for the distance and can be combined with any proved bounds.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

/-- Positive seed dimension supplies a nonzero recurrence word. -/
theorem exists_nonzero_seedWord (s : ℕ) :
    ∃ c : SeedIndex s → ZMod 2, c ∈ seedSpace s ∧ c ≠ 0 := by
  have hd : 0 < Module.finrank (ZMod 2) (seedSpace s) := by
    rw [finrank_seedSpace]
    have hq := two_le_width (Nat.succ_pos s)
    exact lt_of_lt_of_le (by decide : 0 < 2) hq
  obtain ⟨c, hc⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hd
  exact ⟨c.val, c.property, fun h => hc (Subtype.ext h)⟩

/-- Some natural number occurs as the weight of a nonzero seed word. -/
theorem exists_seedWeight (s : ℕ) :
    ∃ d : ℕ, ∃ c : SeedIndex s → ZMod 2,
      c ∈ seedSpace s ∧ c ≠ 0 ∧ hammingNorm c = d := by
  obtain ⟨c, hc, hc0⟩ := exists_nonzero_seedWord s
  exact ⟨hammingNorm c, c, hc, hc0, rfl⟩

/-- The exact minimum weight among the nonzero classical seed words. -/
noncomputable def seedDistance (s : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_seedWeight s)

/-- A nonzero recurrence word attains the classical distance. -/
theorem exists_seedDistance_word (s : ℕ) :
    ∃ c : SeedIndex s → ZMod 2,
      c ∈ seedSpace s ∧ c ≠ 0 ∧ hammingNorm c = seedDistance s := by
  classical
  exact Nat.find_spec (exists_seedWeight s)

/-- Every nonzero recurrence word has at least the classical distance. -/
theorem seedDistance_le_weight (s : ℕ) (c : SeedIndex s → ZMod 2)
    (hc : c ∈ seedSpace s) (hc0 : c ≠ 0) : seedDistance s ≤ hammingNorm c := by
  classical
  exact Nat.find_min' (exists_seedWeight s) ⟨c, hc, hc0, rfl⟩

/-- The exact classical distance is strictly positive. -/
theorem seedDistance_pos (s : ℕ) : 0 < seedDistance s := by
  obtain ⟨c, _, hc0, hw⟩ := exists_seedDistance_word s
  rw [← hw]
  exact hammingNorm_pos_iff.mpr hc0

/-- The classical distance does not exceed the physical period. -/
theorem seedDistance_le_period (s : ℕ) : seedDistance s ≤ period (s + 1) := by
  obtain ⟨c, _, _, hw⟩ := exists_seedDistance_word s
  rw [← hw]
  simpa only [SeedIndex, ZMod.card] using (hammingNorm_le_card_fintype (x := c))

/-- The distance is precisely the least nonzero seed weight. -/
theorem seedDistance_isLeast (s : ℕ) :
    IsLeast {d : ℕ | ∃ c : SeedIndex s → ZMod 2,
      c ∈ seedSpace s ∧ c ≠ 0 ∧ hammingNorm c = d} (seedDistance s) := by
  refine ⟨exists_seedDistance_word s, ?_⟩
  rintro d ⟨c, hc, hc0, rfl⟩
  exact seedDistance_le_weight s c hc hc0

/-- A uniform weight bound also bounds the exact distance. -/
theorem le_seedDistance (s d : ℕ)
    (h : ∀ c : SeedIndex s → ZMod 2, c ∈ seedSpace s → c ≠ 0 → d ≤ hammingNorm c) :
    d ≤ seedDistance s := by
  obtain ⟨c, hc, hc0, hw⟩ := exists_seedDistance_word s
  rw [← hw]
  exact h c hc hc0

end Quantum.Stabilizer.Homological.BB.Fractal

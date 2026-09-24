import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Recurrence
import QEC.Stabilizer.Framework.Homological.SeparableBBChainComplex

/-!
# Circulant checks and the cyclic seed space

The classical check kernel is the recurrence seed space with coordinates
reversed. Reversal preserves Hamming weight. The two physical BB checks are
exactly the horizontal and vertical lifts of this circulant seed check.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open scoped BigOperators Matrix

/-- The one-dimensional trinomial check, as a sum of point masses. -/
noncomputable def seedCheck (s : ℕ) : SeedIndex s → ZMod 2 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single (width (s + 1) : SeedIndex s) 1

/-- The three seed exponents are distinct in the cyclic coordinate. -/
theorem seedExponents_distinct (s : ℕ) :
    (0 : SeedIndex s) ≠ 1 ∧ (0 : SeedIndex s) ≠ width (s + 1) ∧
      (1 : SeedIndex s) ≠ width (s + 1) := by
  have hn : 3 ≤ period (s + 1) := three_le_period (Nat.succ_pos s)
  have hq : 2 ≤ width (s + 1) := two_le_width (Nat.succ_pos s)
  have hqn : width (s + 1) < period (s + 1) := width_lt_period (Nat.succ_pos s)
  have hc {a b : ℕ} (ha : a < period (s + 1)) (hb : b < period (s + 1)) :
      (a : SeedIndex s) = (b : SeedIndex s) ↔ a = b := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.cast_zero, Nat.cast_one] using
      (hc (a := 0) (b := 1) (by omega) (by omega)).not.mpr (by omega)
  · simpa only [Nat.cast_zero] using
      (hc (a := 0) (b := width (s + 1)) (by omega) hqn).not.mpr (by omega)
  · simpa only [Nat.cast_one] using
      (hc (a := 1) (b := width (s + 1)) (by omega) hqn).not.mpr (by omega)

/-- The point-mass sum is the indicator of the three seed exponents. -/
theorem seedCheck_eq_indicator (s : ℕ) (i : SeedIndex s) :
    seedCheck s i = if i = 0 ∨ i = 1 ∨ i = width (s + 1) then 1 else 0 := by
  obtain ⟨h01, h0q, h1q⟩ := seedExponents_distinct s
  by_cases hi0 : i = 0
  · subst i
    simp [seedCheck, h01, h0q]
  by_cases hi1 : i = 1
  · subst i
    simp [seedCheck, h01.symm, h1q]
  by_cases hiq : i = width (s + 1)
  · subst i
    simp [seedCheck, h0q.symm, h1q.symm]
  · simp [seedCheck, hi0, hi1, hiq]

/-- The actual horizontal check is the separable lift of the seed check. -/
theorem checkA_eq_horizontal (s : ℕ) :
    checkA s = SeparableBB.horizontal (J := SeedIndex s) (seedCheck s) := by
  funext p
  rcases p with ⟨i, j⟩
  by_cases hj : j = 0
  · subst j
    simp [checkA, aSupport, SeparableBB.horizontal, seedCheck_eq_indicator]
  · simp [checkA, aSupport, SeparableBB.horizontal, hj]

/-- The actual vertical check is the separable lift of the seed check. -/
theorem checkB_eq_vertical (s : ℕ) :
    checkB s = SeparableBB.vertical (I := SeedIndex s) (seedCheck s) := by
  funext p
  rcases p with ⟨i, j⟩
  by_cases hi : i = 0
  · subst i
    simp [checkB, bSupport, SeparableBB.vertical, seedCheck_eq_indicator]
  · simp [checkB, bSupport, SeparableBB.vertical, hi]

/-- The concrete fractal complex is the separable BB complex of its seed. -/
theorem chainComplex_eq_separable (s : ℕ) :
    chainComplex s = SeparableBB.complex (seedCheck s) (seedCheck s) := by
  rw [chainComplex, checkA_eq_horizontal, checkB_eq_vertical]
  unfold SeparableBB.complex
  congr 1

/-- A seed-check circulant acts by the three backward shifts. -/
theorem seedCheck_mulVec (s : ℕ) (c : SeedIndex s → ZMod 2) (j : SeedIndex s) :
    (Matrix.circulant (seedCheck s) *ᵥ c) j =
      c j + c (j - 1) + c (j - (width (s + 1) : SeedIndex s)) := by
  have hconv : Matrix.circulant (seedCheck s) *ᵥ c = conv (seedCheck s) c := by
    rw [conv_comm]
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.circulant_apply, conv, mul_comm]
  rw [hconv]
  rw [seedCheck, conv_add_left, conv_add_left]
  simp only [Pi.add_apply, conv_single_left_apply, sub_zero]

/-- Reversal of the cyclic coordinate as a linear equivalence. -/
def reverseWord (s : ℕ) : (SeedIndex s → ZMod 2) ≃ₗ[ZMod 2] (SeedIndex s → ZMod 2) where
  toFun c j := c (-j)
  invFun c j := c (-j)
  left_inv c := by ext j; simp
  right_inv c := by ext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reversal evaluates a word at the negative cyclic index. -/
@[simp] theorem reverseWord_apply (s : ℕ) (c : SeedIndex s → ZMod 2) (j : SeedIndex s) :
    reverseWord s c j = c (-j) := rfl

/-- Reversing twice restores the original word. -/
@[simp] theorem reverseWord_reverseWord (s : ℕ) (c : SeedIndex s → ZMod 2) :
    reverseWord s (reverseWord s c) = c := by
  ext j
  simp

/-- A check-kernel word is precisely a reversed recurrence word. -/
theorem seedCheck_mulVec_eq_zero_iff (s : ℕ) (c : SeedIndex s → ZMod 2) :
    Matrix.circulant (seedCheck s) *ᵥ c = 0 ↔ reverseWord s c ∈ seedSpace s := by
  rw [mem_seedSpace_iff]
  have hb := (by decide : ∀ a b c : ZMod 2, a + b + c = 0 ↔ c = a + b)
  constructor
  · intro hc j
    have h := congrFun hc (-j)
    rw [seedCheck_mulVec] at h
    simpa only [reverseWord_apply, neg_add, sub_eq_add_neg, Pi.zero_apply] using
      (hb _ _ _).mp h
  · intro hc
    funext j
    rw [seedCheck_mulVec]
    apply (hb _ _ _).mpr
    simpa only [reverseWord_apply, neg_add, neg_neg, sub_eq_add_neg] using hc (-j)

/-- Reversal identifies the circulant kernel with the recurrence seed space. -/
noncomputable def seedKernelEquiv (s : ℕ) :
    LinearMap.ker (Matrix.toLin' (Matrix.circulant (seedCheck s))) ≃ₗ[ZMod 2]
      seedSpace s where
  toFun c := ⟨reverseWord s c.val,
    (seedCheck_mulVec_eq_zero_iff s c.val).mp c.property⟩
  invFun c := ⟨reverseWord s c.val, (seedCheck_mulVec_eq_zero_iff s _).mpr
    (by rw [reverseWord_reverseWord]; exact c.property)⟩
  left_inv c := Subtype.ext (reverseWord_reverseWord s c.val)
  right_inv c := Subtype.ext (reverseWord_reverseWord s c.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual circulant check has the advertised classical nullity. -/
theorem finrank_seedCheck_kernel (s : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' (Matrix.circulant (seedCheck s)))) =
      width (s + 1) :=
  (seedKernelEquiv s).finrank_eq.trans (finrank_seedSpace s)

/-- Coordinate reversal preserves Hamming weight. -/
theorem hammingNorm_reverseWord (s : ℕ) (c : SeedIndex s → ZMod 2) :
    hammingNorm (reverseWord s c) = hammingNorm c := by
  exact card_filter_comp_equiv (Equiv.neg (SeedIndex s)) (fun i => c i ≠ 0)

/-- Any proved seed-space weight bound holds for the actual check kernel. -/
theorem seedCheck_kernel_weight_ge (s d : ℕ)
    (hd : ∀ c ∈ seedSpace s, c ≠ 0 → d ≤ hammingNorm c)
    (c : SeedIndex s → ZMod 2) (hc : Matrix.circulant (seedCheck s) *ᵥ c = 0)
    (hc0 : c ≠ 0) : d ≤ hammingNorm c := by
  rw [← hammingNorm_reverseWord s c]
  apply hd _ ((seedCheck_mulVec_eq_zero_iff s c).mp hc)
  intro h
  apply hc0
  have hi := congrArg (reverseWord s) h
  simpa using hi

end Quantum.Stabilizer.Homological.BB.Fractal

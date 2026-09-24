import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-!
# Averaging sparse observations over a finite translation group

If every translated observation has weight at least `L`, and each observation
coordinate is the sum of at most `s` physical coordinates, double counting
bounds `L` by the physical weight. The argument keeps every translation and
uses no metric assumption on a change of basis.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open scoped BigOperators

/-- Indicator that a binary coefficient is nonzero. -/
def nonzeroIndicator (z : ZMod 2) : ℕ := if z ≠ 0 then 1 else 0

/-- Hamming weight is the sum of nonzero-coordinate indicators. -/
lemma hammingNorm_eq_sum_indicator {I : Type*} [Fintype I] (c : I → ZMod 2) :
    hammingNorm c = ∑ i, nonzeroIndicator (c i) := by
  classical
  simp only [hammingNorm, nonzeroIndicator, Finset.sum_boole, Nat.cast_id]

/-- A nonzero sum requires at least one nonzero summand. -/
lemma indicator_sum_le {I : Type*} [Fintype I] (c : I → ZMod 2) :
    nonzeroIndicator (∑ i, c i) ≤ ∑ i, nonzeroIndicator (c i) := by
  classical
  by_cases h : ∑ i, c i = 0
  · simp [nonzeroIndicator, h]
  · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (nonzeroIndicator (c j)))
      (Finset.mem_univ i)
    simpa [nonzeroIndicator, h, hi] using hle

variable {G E : Type*} [Fintype G] [AddCommGroup G] [Fintype E]

/-- Translating the physical coordinates preserves their total indicator sum. -/
lemma sum_indicator_translate (c : G → ZMod 2) (r : G) :
    (∑ j, nonzeroIndicator (c (j + r))) = hammingNorm c := by
  classical
  rw [hammingNorm_eq_sum_indicator]
  exact Fintype.sum_equiv (Equiv.addRight r) _ _ (fun _ => rfl)

/-- An observation coordinate is a finite sum of translated physical sites. -/
def sparseObservation (lengths : E → ℕ) (offsets : ∀ e, Fin (lengths e) → G)
    (c : G → ZMod 2) (j : G) (e : E) : ZMod 2 :=
  ∑ i, c (j + offsets e i)

/-- The sum of observation weights is bounded by the total number of taps
multiplied by the physical Hamming weight. -/
theorem sum_observation_weight_le
    (lengths : E → ℕ) (offsets : ∀ e, Fin (lengths e) → G)
    (c : G → ZMod 2) :
    (∑ j, hammingNorm (sparseObservation lengths offsets c j)) ≤
      (∑ e, lengths e) * hammingNorm c := by
  classical
  simp only [hammingNorm_eq_sum_indicator, sparseObservation]
  calc
    (∑ j : G, ∑ e : E, nonzeroIndicator (∑ i : Fin (lengths e), c (j + offsets e i)))
        ≤ ∑ j : G, ∑ e : E, ∑ i : Fin (lengths e), nonzeroIndicator (c (j + offsets e i)) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun e _ => indicator_sum_le _
    _ = ∑ e : E, ∑ i : Fin (lengths e), ∑ j : G, nonzeroIndicator (c (j + offsets e i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]
    _ = (∑ e : E, lengths e) * ∑ j : G, nonzeroIndicator (c j) := by
      simp only [sum_indicator_translate, hammingNorm_eq_sum_indicator, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_mul]

/-- A lower bound on every translated observation gives a physical weight bound. -/
theorem sparse_observation_averaging
    (lengths : E → ℕ) (offsets : ∀ e, Fin (lengths e) → G)
    (c : G → ZMod 2) (L s : ℕ)
    (hL : ∀ j, L ≤ hammingNorm (sparseObservation lengths offsets c j))
    (hs : ∀ e, lengths e ≤ s) :
    Fintype.card G * L ≤ Fintype.card E * s * hammingNorm c := by
  classical
  calc
    Fintype.card G * L = ∑ _j : G, L := by simp
    _ ≤ ∑ j : G, hammingNorm (sparseObservation lengths offsets c j) :=
      Finset.sum_le_sum fun j _ => hL j
    _ ≤ (∑ e : E, lengths e) * hammingNorm c := sum_observation_weight_le lengths offsets c
    _ ≤ (Fintype.card E * s) * hammingNorm c := by
      apply Nat.mul_le_mul_right
      simpa using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hs e)

/-- At most twice as many observation coordinates as translations yields the
integer distance estimate used by the fractal family. -/
theorem sparse_observation_lower_bound
    (lengths : E → ℕ) (offsets : ∀ e, Fin (lengths e) → G)
    (c : G → ZMod 2) (L s : ℕ)
    (hL : ∀ j, L ≤ hammingNorm (sparseObservation lengths offsets c j))
    (hs : ∀ e, lengths e ≤ s)
    (hcard : Fintype.card E ≤ 2 * Fintype.card G) :
    L ≤ 2 * s * hammingNorm c := by
  have h := sparse_observation_averaging lengths offsets c L s hL hs
  have h' : Fintype.card G * L ≤ Fintype.card G * (2 * s * hammingNorm c) := by
    calc
      Fintype.card G * L ≤ Fintype.card E * s * hammingNorm c := h
      _ ≤ (2 * Fintype.card G) * s * hammingNorm c := by gcongr
      _ = Fintype.card G * (2 * s * hammingNorm c) := by ring
  exact Nat.le_of_mul_le_mul_left h' Fintype.card_pos

end Quantum.Stabilizer.Homological.BB.Fractal

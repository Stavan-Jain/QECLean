import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# The fractal cyclic seed polynomial

For `q = 2^s`, the trinomial `1 + X + X^q` divides `X^(q^2 - 1) + 1`.
This file proves the algebraic identity underlying the weight-six separable
BB candidate. It does not assert its conjectured minimum-distance formula.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Polynomial

/-- The power-of-two recurrence length. -/
def width (s : ℕ) : ℕ := 2 ^ s

/-- The odd cyclic period of the fractal seed. -/
def period (s : ℕ) : ℕ := width s ^ 2 - 1

/-- The three-term cyclic check polynomial. -/
noncomputable def checkPolynomial (s : ℕ) : (ZMod 2)[X] := 1 + X + X ^ width s

/-- The recurrence length is positive at every index. -/
lemma width_pos (s : ℕ) : 0 < width s := by
  unfold width
  positivity

/-- Frobenius produces the exact period relation. -/
theorem checkPolynomial_pow_add (s : ℕ) :
    checkPolynomial s ^ width s + checkPolynomial s =
      (X : (ZMod 2)[X]) ^ (width s ^ 2) + X := by
  unfold checkPolynomial width
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, ← pow_mul]
  rw [pow_two]
  simp only [add_assoc, add_left_comm, add_comm, CharTwo.add_cancel_left]

/-- The cyclic check is relatively prime to the coordinate monomial. -/
lemma checkPolynomial_isCoprime_X (s : ℕ) :
    IsCoprime (checkPolynomial s) (X : (ZMod 2)[X]) := by
  refine ⟨1, 1 + X ^ (width s - 1), ?_⟩
  have hpow : (X : (ZMod 2)[X]) ^ (width s - 1) * X = X ^ width s := by
    rw [← pow_succ, Nat.sub_add_cancel (width_pos s)]
  simp only [one_mul, add_mul, hpow, checkPolynomial]
  simp only [add_assoc, add_left_comm, add_comm, CharTwo.add_self_eq_zero, zero_add]

/-- The check polynomial divides the claimed cyclic period polynomial. -/
theorem checkPolynomial_dvd_period (s : ℕ) :
    checkPolynomial s ∣ (X : (ZMod 2)[X]) ^ period s + 1 := by
  have hdiv : checkPolynomial s ∣
      (X : (ZMod 2)[X]) ^ (width s ^ 2) + X := by
    rw [← checkPolynomial_pow_add]
    exact dvd_add (dvd_pow_self _ (width_pos s).ne') (dvd_refl _)
  have hperiod : (X : (ZMod 2)[X]) * (X ^ period s + 1) =
      X ^ (width s ^ 2) + X := by
    rw [mul_add, mul_one, period, ← pow_succ']
    rw [Nat.sub_add_cancel (by have := width_pos s; nlinarith : 1 ≤ width s ^ 2)]
  rw [← hperiod] at hdiv
  exact (checkPolynomial_isCoprime_X s).dvd_of_dvd_mul_left hdiv

/-- Positive indices have recurrence length at least two. -/
lemma two_le_width {s : ℕ} (hs : 0 < s) : 2 ≤ width s := by
  cases s with
  | zero => omega
  | succ s =>
    have h := width_pos s
    simp only [width, pow_succ] at *
    omega

/-- Every positive-index cyclic period is at least three. -/
lemma three_le_period {s : ℕ} (hs : 0 < s) : 3 ≤ period s := by
  have h := two_le_width hs
  have hsq : 1 ≤ width s ^ 2 := by nlinarith
  have he := Nat.sub_add_cancel hsq
  change 3 ≤ width s ^ 2 - 1
  nlinarith

/-- The trinomial's three exponents remain distinct on the cyclic period. -/
lemma width_lt_period {s : ℕ} (hs : 0 < s) : width s < period s := by
  have h := two_le_width hs
  have hsq : 1 ≤ width s ^ 2 := by nlinarith
  have he := Nat.sub_add_cancel hsq
  change width s < width s ^ 2 - 1
  nlinarith

end Quantum.Stabilizer.Homological.BB.Fractal

import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Recurrence
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Truncation
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Pascal
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Averaging
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Physical realization of open Pascal histories

Every translated seed word determines a nonzero initial polynomial. Its open
Pascal history is a sparse observation of the physical cyclic word.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Polynomial
open scoped BigOperators

/-- Translate a functional by multiplication with a cyclic coordinate unit. -/
noncomputable def shiftedFunctional (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (j : SeedIndex s) :
    Module.Dual (ZMod 2) (SeedAlgebra s) where
  toFun x := f (seedPower s j * x)
  map_add' x y := by simp [mul_add]
  map_smul' a x := by simp

/-- Translating back cancels a functional translation. -/
theorem shiftedFunctional_cancel (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (j : SeedIndex s) :
    shiftedFunctional s (shiftedFunctional s f j) (-j) = f := by
  ext x
  change f (seedPower s j * (seedPower s (-j) * x)) = f x
  rw [← mul_assoc, ← seedPower_add]
  simp

/-- A nonzero functional stays nonzero under every cyclic translation. -/
theorem shiftedFunctional_ne_zero (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (hf : f ≠ 0) (j : SeedIndex s) :
    shiftedFunctional s f j ≠ 0 := by
  intro h
  have hc := shiftedFunctional_cancel s f j
  rw [h] at hc
  apply hf
  exact hc.symm.trans (by ext x; rfl)

/-- The polynomial recording the initial coordinates of a functional. -/
noncomputable def initialPolynomial (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) : (ZMod 2)[X] :=
  ofFn (width (s + 1)) fun i => f (seedRoot s ^ (i : ℕ))

/-- Initial polynomials have degree below the recurrence length. -/
theorem initialPolynomial_natDegree_lt (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) :
    (initialPolynomial s f).natDegree < width (s + 1) :=
  ofFn_natDegree_lt (width_pos _) _

/-- Nonzero functionals have nonzero initial polynomials. -/
theorem initialPolynomial_ne_zero (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (hf : f ≠ 0) :
    initialPolynomial s f ≠ 0 := by
  intro h
  apply hf
  apply (seedBasis s).ext
  intro i
  have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff (i : ℕ)) h
  simpa only [initialPolynomial, ofFn_coeff_eq_val_of_lt _ i.isLt,
    coeff_zero, seedBasis_apply, LinearMap.zero_apply] using hc

/-- Evaluating a monomial in the recurrence algebra then applying a functional
is scalar multiplication of a physical root coordinate. -/
lemma functional_mk_monomial (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (i : ℕ) (a : ZMod 2) :
    f (AdjoinRoot.mk (checkPolynomial (s + 1)) (monomial i a)) =
      a * f (seedRoot s ^ i) := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X]
  rw [AdjoinRoot.mk_C]
  change f (algebraMap (ZMod 2) (SeedAlgebra s) a * (seedRoot s ^ i)) = _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- An open-history coefficient is the corresponding quotient-algebra
coordinate functional. -/
theorem initialPolynomial_history_coeff (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (t r : ℕ) :
    (initialPolynomial s f * (1 + Polynomial.X) ^ (t : ℕ)).coeff r =
      f (AdjoinRoot.mk (checkPolynomial (s + 1)) (historyFunctional (s + 1) t r)) := by
  classical
  rw [initialPolynomial, ofFn_eq_sum_monomial, Finset.sum_mul, finsetSum_coeff]
  simp only [historyFunctional, map_sum, functional_mk_monomial]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  rw [coeff_one_add_X_pow]
  split_ifs <;> simp_all [mul_comm]

/-- The finite set of coordinates in an open history. -/
abbrev HistoryIndex (s : ℕ) :=
  Fin (width (s + 1)) × Fin (2 * width (s + 1) - 1)

/-- Coefficients of all open-history rows. -/
noncomputable def openHistory (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (e : HistoryIndex s) : ZMod 2 :=
  (initialPolynomial s f * (1 + Polynomial.X) ^ (e.1 : ℕ)).coeff (e.2 : ℕ)

/-- Polynomial support inside a finite interval is its coefficient Hamming weight. -/
lemma support_card_eq_coeff_hamming (p : (ZMod 2)[X]) (n : ℕ)
    (hp : p.natDegree < n) :
    p.support.card = hammingNorm (fun i : Fin n => p.coeff (i : ℕ)) := by
  classical
  rw [hammingNorm_eq_sum_indicator, ← Finset.sum_range (fun i => nonzeroIndicator (p.coeff i))]
  have heq : p.support = (Finset.range n).filter (fun i => p.coeff i ≠ 0) := by
    ext i
    simp only [mem_support_iff, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hi => ⟨(le_natDegree_of_ne_zero hi).trans_lt hp, hi⟩, fun hi => hi.2⟩
  rw [heq]
  simp only [nonzeroIndicator, Finset.sum_boole, Nat.cast_id]

/-- Every nonzero functional has a full open-history weight of at least the
Sierpinski count. -/
theorem openHistory_weight_ge (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (hf : f ≠ 0) :
    3 ^ (s + 1) ≤ hammingNorm (openHistory s f) := by
  have hp := polynomial_open_history_weight_ge (s + 1) (initialPolynomial s f)
    (initialPolynomial_natDegree_lt s f) (initialPolynomial_ne_zero s f hf)
  convert hp using 1
  rw [hammingNorm_eq_sum_indicator, Fintype.sum_prod_type]
  change (∑ t : Fin (width (s + 1)), ∑ r : Fin (2 * width (s + 1) - 1),
      nonzeroIndicator ((initialPolynomial s f * (1 + Polynomial.X) ^ (t : ℕ)).coeff (r : ℕ))) = _
  rw [show 2 ^ (s + 1) = width (s + 1) from rfl, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t _
  symm
  rw [support_card_eq_coeff_hamming _ (2 * width (s + 1) - 1),
    hammingNorm_eq_sum_indicator]
  have hdeg := initialPolynomial_natDegree_lt s f
  have hq := width_pos (s + 1)
  have ht' := t.isLt
  have h := natDegree_mul_le (p := initialPolynomial s f) (q := (1 + Polynomial.X) ^ (t : ℕ))
  have hpow : ((1 + (Polynomial.X : (ZMod 2)[X])) ^ (t : ℕ)).natDegree ≤ (t : ℕ) := by
    calc
      _ ≤ (t : ℕ) * (1 + (Polynomial.X : (ZMod 2)[X])).natDegree := natDegree_pow_le
      _ = (t : ℕ) := by
        rw [add_comm (1 : (ZMod 2)[X]) Polynomial.X, ← C_1, natDegree_X_add_C, mul_one]
  dsimp [width] at *
  omega

end Quantum.Stabilizer.Homological.BB.Fractal

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-!
# Binary Pascal weight estimates

The recursive Pascal transform has blocks `[[P, P], [0, P]]`.
Its first nonzero principal coefficient controls its Hamming weight.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Finset

/-- The weight of a binary value. -/
def bitWeight (a : ZMod 2) : ℕ := if a = 0 then 0 else 1

/-- The coefficient weight on a finite initial interval. -/
def intervalWeight (n : ℕ) (a : ℕ → ZMod 2) : ℕ :=
  ∑ i ∈ range n, bitWeight (a i)

/-- The binary Pascal transform, split at the highest binary digit. -/
def pascalTransform : ℕ → (ℕ → ZMod 2) → ℕ → ZMod 2
  | 0, a, _ => a 0
  | s + 1, a, i =>
    if i < 2 ^ s then
      pascalTransform s a i + pascalTransform s (fun j => a (2 ^ s + j)) i
    else pascalTransform s (fun j => a (2 ^ s + j)) (i - 2 ^ s)

/-- The weight of a principal Pascal row, expressed by binary recursion. -/
def principalWeight : ℕ → ℕ → ℕ
  | 0, _ => 1
  | s + 1, i =>
    if i < 2 ^ s then principalWeight s i
    else 2 * principalWeight s (i - 2 ^ s)

/-- The scalar triangle inequality for the binary coefficient weight. -/
lemma bitWeight_add_le (a b : ZMod 2) :
    bitWeight (a + b) ≤ bitWeight a + bitWeight b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [bitWeight, if_neg ha, if_neg hb]
  split_ifs <;> omega

/-- Recovering one summand gives the reverse binary triangle inequality. -/
lemma bitWeight_le_add (a b : ZMod 2) :
    bitWeight a ≤ bitWeight (a + b) + bitWeight b := by
  simpa only [CharTwo.add_cancel_right] using bitWeight_add_le (a + b) b

/-- The weight of a concatenated interval is the sum of its two parts. -/
lemma intervalWeight_add (m n : ℕ) (a : ℕ → ZMod 2) :
    intervalWeight (m + n) a =
      intervalWeight m a + intervalWeight n (fun i => a (m + i)) := by
  simp only [intervalWeight, sum_range_add]

/-- Pointwise equality on the interval preserves its coefficient weight. -/
lemma intervalWeight_congr {n : ℕ} {a b : ℕ → ZMod 2}
    (h : ∀ i < n, a i = b i) : intervalWeight n a = intervalWeight n b := by
  apply sum_congr rfl
  intro i hi
  rw [h i (mem_range.mp hi)]

/-- The binary triangle inequality summed over a finite interval. -/
lemma intervalWeight_le_add (n : ℕ) (a b : ℕ → ZMod 2) :
    intervalWeight n a ≤
      intervalWeight n (fun i => a i + b i) + intervalWeight n b := by
  simp only [intervalWeight, ← sum_add_distrib]
  exact sum_le_sum fun i _ => bitWeight_le_add (a i) (b i)

/-- The Pascal transform of a zero interval is zero on that interval. -/
lemma pascalTransform_zero (s : ℕ) (a : ℕ → ZMod 2)
    (h : ∀ i < 2 ^ s, a i = 0) :
    ∀ i < 2 ^ s, pascalTransform s a i = 0 := by
  induction s generalizing a with
  | zero =>
    intro i hi
    simpa only [pascalTransform] using h 0 (by simp)
  | succ s ih =>
    intro i hi
    have hleft : ∀ j < 2 ^ s, a j = 0 := by
      intro j hj
      apply h
      rw [pow_succ]
      omega
    have hright : ∀ j < 2 ^ s, a (2 ^ s + j) = 0 := by
      intro j hj
      apply h
      rw [pow_succ]
      omega
    simp only [pascalTransform]
    split_ifs with hil
    · rw [ih a hleft i hil, ih _ hright i hil, zero_add]
    · have hisub : i - 2 ^ s < 2 ^ s := by
        rw [pow_succ] at hi
        omega
      exact ih _ hright _ hisub

/-- The weight of a transformed block splits into its two Pascal halves. -/
lemma intervalWeight_pascalTransform_succ (s : ℕ) (a : ℕ → ZMod 2) :
    intervalWeight (2 ^ (s + 1)) (pascalTransform (s + 1) a) =
      intervalWeight (2 ^ s) (fun i => pascalTransform s a i +
        pascalTransform s (fun j => a (2 ^ s + j)) i) +
      intervalWeight (2 ^ s) (pascalTransform s (fun j => a (2 ^ s + j))) := by
  rw [pow_succ, Nat.mul_two, intervalWeight_add]
  congr 1
  · apply intervalWeight_congr
    intro i hi
    simp only [pascalTransform, if_pos hi]
  · apply intervalWeight_congr
    intro i hi
    simp only [pascalTransform, Nat.not_lt.mpr (Nat.le_add_right _ _), if_false,
      Nat.add_sub_cancel_left]

/-- The first nonzero principal coefficient controls Pascal weight. -/
theorem principalWeight_le_transform (s : ℕ) (a : ℕ → ZMod 2) (r : ℕ)
    (hr : r < 2 ^ s) (har : a r ≠ 0) (hbefore : ∀ i < r, a i = 0) :
    principalWeight s r ≤ intervalWeight (2 ^ s) (pascalTransform s a) := by
  induction s generalizing a r with
  | zero =>
    have hr0 : r = 0 := by simpa using hr
    subst r
    simp [principalWeight, intervalWeight, pascalTransform, bitWeight, har]
  | succ s ih =>
    rw [intervalWeight_pascalTransform_succ]
    simp only [principalWeight]
    split_ifs with hrl
    · exact (ih a r hrl har hbefore).trans
        (intervalWeight_le_add _ _ _)
    · have hrr : r - 2 ^ s < 2 ^ s := by
        rw [pow_succ] at hr
        omega
      have hright : (fun j => a (2 ^ s + j)) (r - 2 ^ s) ≠ 0 := by
        simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt hrl)] using har
      have hrightBefore : ∀ i < r - 2 ^ s, a (2 ^ s + i) = 0 := by
        intro i hi
        apply hbefore
        omega
      have hleft : ∀ i < 2 ^ s, pascalTransform s a i = 0 := by
        apply pascalTransform_zero
        intro i hi
        apply hbefore
        omega
      have hw := ih _ _ hrr hright hrightBefore
      have heq : intervalWeight (2 ^ s) (fun i => pascalTransform s a i +
          pascalTransform s (fun j => a (2 ^ s + j)) i) =
          intervalWeight (2 ^ s) (pascalTransform s (fun j => a (2 ^ s + j))) := by
        apply intervalWeight_congr
        intro i hi
        rw [hleft i hi, zero_add]
      rw [heq]
      omega

/-- The total weight of all principal rows is the Sierpinski count. -/
theorem sum_principalWeight (s : ℕ) :
    ∑ i ∈ range (2 ^ s), principalWeight s i = 3 ^ s := by
  induction s with
  | zero => simp [principalWeight]
  | succ s ih =>
    rw [pow_succ, Nat.mul_two, sum_range_add]
    have hleft : ∑ i ∈ range (2 ^ s), principalWeight (s + 1) i = 3 ^ s := by
      convert ih using 1
      apply sum_congr rfl
      intro i hi
      simp only [principalWeight, if_pos (mem_range.mp hi)]
    have hright : ∑ i ∈ range (2 ^ s), principalWeight (s + 1) (2 ^ s + i) =
        2 * 3 ^ s := by
      simp only [principalWeight, Nat.not_lt.mpr (Nat.le_add_right _ _), if_false,
        Nat.add_sub_cancel_left, ← mul_sum, ih]
    rw [hleft]
    rw [hright, pow_succ]
    omega

/-- A principal row below the new binary digit retains its old weight. -/
lemma principalWeight_small (s i : ℕ) (hi : i < 2 ^ s) :
    principalWeight (s + 1) i = principalWeight s i := by
  simp only [principalWeight, if_pos hi]

/-- Setting the new highest binary digit doubles principal weight. -/
lemma principalWeight_width_add (s i : ℕ) :
    principalWeight (s + 1) (2 ^ s + i) = 2 * principalWeight s i := by
  simp only [principalWeight, Nat.not_lt.mpr (Nat.le_add_right _ _), if_false,
    Nat.add_sub_cancel_left]

/-- Any full-width interval of principal rows has Sierpinski weight. -/
theorem sum_principalWeight_shift_ge (s r : ℕ) (hr : r < 2 ^ s) :
    3 ^ s ≤ ∑ i ∈ range (2 ^ s), principalWeight (s + 1) (r + i) := by
  have hsmall : ∑ i ∈ range (2 ^ s), principalWeight (s + 1) i = 3 ^ s := by
    convert sum_principalWeight s using 1
    apply sum_congr rfl
    intro i hi
    exact principalWeight_small s i (mem_range.mp hi)
  have hrsmall : ∑ i ∈ range r, principalWeight (s + 1) i =
      ∑ i ∈ range r, principalWeight s i := by
    apply sum_congr rfl
    intro i hi
    exact principalWeight_small s i (lt_trans (mem_range.mp hi) hr)
  have hhigh : ∑ i ∈ range r, principalWeight (s + 1) (2 ^ s + i) =
      2 * ∑ i ∈ range r, principalWeight s i := by
    simp only [principalWeight_width_add, mul_sum]
  have hsplit : (∑ i ∈ range r, principalWeight (s + 1) i) +
      (∑ i ∈ range (2 ^ s), principalWeight (s + 1) (r + i)) =
      (∑ i ∈ range (2 ^ s), principalWeight (s + 1) i) +
      (∑ i ∈ range r, principalWeight (s + 1) (2 ^ s + i)) := by
    rw [← sum_range_add, ← sum_range_add, Nat.add_comm r]
  rw [hsmall, hrsmall, hhigh] at hsplit
  omega

/-- Shifting principal coefficients generates a complete open Pascal history. -/
theorem pascal_history_weight_ge (s : ℕ) (a : ℕ → ZMod 2) (r : ℕ)
    (hr : r < 2 ^ s) (har : a r ≠ 0) (hbefore : ∀ i < r, a i = 0) :
    3 ^ s ≤ ∑ t ∈ range (2 ^ s), intervalWeight (2 ^ (s + 1))
      (pascalTransform (s + 1) (fun j => if t ≤ j then a (j - t) else 0)) := by
  apply (sum_principalWeight_shift_ge s r hr).trans
  apply sum_le_sum
  intro t ht
  apply principalWeight_le_transform (s + 1) _ (r + t)
  · rw [pow_succ]
    have := mem_range.mp ht
    omega
  · simpa only [Nat.le_add_left, if_true, Nat.add_sub_cancel_right] using har
  · intro i hi
    split_ifs with hti
    · apply hbefore
      omega
    · rfl

open Polynomial

/-- The polynomial represented in the principal Pascal basis. -/
noncomputable def principalCombination (s : ℕ) (a : ℕ → ZMod 2) : (ZMod 2)[X] :=
  ∑ j ∈ range (2 ^ s), C (a j) * (1 + X) ^ j

/-- A principal combination fits in its stated coefficient interval. -/
lemma principalCombination_natDegree_lt (s : ℕ) (a : ℕ → ZMod 2) :
    (principalCombination s a).natDegree < 2 ^ s := by
  have hpos : 0 < 2 ^ s := by positivity
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_)
    (Nat.sub_lt hpos (by decide : 0 < 1))
  intro i hi
  have hdeg : ((1 + X : (ZMod 2)[X]) ^ i).natDegree = i := by
    rw [natDegree_pow]
    have hX : (1 + X : (ZMod 2)[X]).natDegree = 1 := by
      simpa only [map_one, add_comm] using (natDegree_X_add_C (R := ZMod 2) 1)
    rw [hX, Nat.mul_one]
  exact (natDegree_C_mul_le _ _).trans (hdeg.le.trans (by
    have := mem_range.mp hi
    omega))

/-- A principal combination splits into its two binary Pascal blocks. -/
lemma principalCombination_succ (s : ℕ) (a : ℕ → ZMod 2) :
    principalCombination (s + 1) a = principalCombination s a +
      (1 + X ^ (2 ^ s)) * principalCombination s (fun i => a (2 ^ s + i)) := by
  unfold principalCombination
  rw [pow_succ, Nat.mul_two, sum_range_add]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [pow_add, add_pow_char_pow, one_pow]
  ring

/-- Recursive Pascal coordinates equal polynomial coefficients. -/
theorem principalCombination_coeff (s : ℕ) (a : ℕ → ZMod 2) (i : ℕ)
    (hi : i < 2 ^ s) :
    (principalCombination s a).coeff i = pascalTransform s a i := by
  induction s generalizing a i with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    simp [principalCombination, pascalTransform]
  | succ s ih =>
    rw [principalCombination_succ, add_mul, one_mul]
    simp only [coeff_add, coeff_X_pow_mul', pascalTransform]
    by_cases hil : i < 2 ^ s
    · simp only [if_pos hil, if_neg (Nat.not_le.mpr hil)]
      rw [ih a i hil, ih _ i hil, add_zero]
    · simp only [if_neg hil, if_pos (Nat.le_of_not_gt hil)]
      have hiz : (principalCombination s a).coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt
          ((principalCombination_natDegree_lt s a).trans_le (Nat.le_of_not_gt hil))
      have hiz' : (principalCombination s (fun j => a (2 ^ s + j))).coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt
          ((principalCombination_natDegree_lt s _).trans_le (Nat.le_of_not_gt hil))
      rw [hiz, hiz', zero_add, zero_add]
      apply ih
      rw [pow_succ] at hi
      omega

/-- Finite coefficient weight equals polynomial support cardinality. -/
lemma intervalWeight_coeff (p : (ZMod 2)[X]) (n : ℕ) (hp : p.natDegree < n) :
    intervalWeight n p.coeff = p.support.card := by
  have hs : p.support = (range n).filter (fun i => p.coeff i ≠ 0) := by
    ext i
    simp only [mem_support_iff, mem_filter, mem_range]
    constructor
    · intro hi
      exact ⟨(le_natDegree_of_ne_zero hi).trans_lt hp, hi⟩
    · exact And.right
  rw [hs, card_filter]
  apply sum_congr rfl
  intro i hi
  simp only [bitWeight, ite_not]

/-- The polynomial Pascal transform has the recursive coefficient weight. -/
lemma principalCombination_weight (s : ℕ) (a : ℕ → ZMod 2) :
    (principalCombination s a).support.card =
      intervalWeight (2 ^ s) (pascalTransform s a) := by
  rw [← intervalWeight_coeff _ _ (principalCombination_natDegree_lt s a)]
  apply intervalWeight_congr
  exact principalCombination_coeff s a

/-- Polynomial substitution realizes a principal combination. -/
lemma principalCombination_coeff_eq_comp (s : ℕ) (p : (ZMod 2)[X])
    (hp : p.natDegree < 2 ^ s) :
    principalCombination s p.coeff = p.comp (1 + X) := by
  nth_rw 2 [p.as_sum_range_C_mul_X_pow' hp]
  simp only [Polynomial.sum_comp, mul_comp, C_comp, X_pow_comp, principalCombination]

/-- Substitution by `1 + X` preserves the polynomial degree bound. -/
lemma natDegree_comp_one_add_X_le (p : (ZMod 2)[X]) :
    (p.comp (1 + X)).natDegree ≤ p.natDegree := by
  convert natDegree_comp_le (p := p) (q := (1 + X : (ZMod 2)[X])) using 1
  have hX : (1 + X : (ZMod 2)[X]).natDegree = 1 := by
    simpa only [map_one, add_comm] using (natDegree_X_add_C (R := ZMod 2) 1)
  rw [hX, Nat.mul_one]

/-- In characteristic two, substitution by `1 + X` is an involution. -/
lemma comp_one_add_X_twice (p : (ZMod 2)[X]) :
    (p.comp (1 + X)).comp (1 + X) = p := by
  rw [comp_assoc, add_comp, one_comp, X_comp]
  simp only [CharTwo.add_cancel_left, comp_X]

/-- Every nonzero binary open Pascal history has Sierpinski weight. -/
theorem polynomial_open_history_weight_ge (s : ℕ) (p : (ZMod 2)[X])
    (hp : p.natDegree < 2 ^ s) (hp0 : p ≠ 0) :
    3 ^ s ≤ ∑ t ∈ range (2 ^ s), (p * (1 + X) ^ t).support.card := by
  let a := p.comp (1 + X)
  have ha : a.natDegree < 2 ^ s :=
    (natDegree_comp_one_add_X_le p).trans_lt hp
  have ha0 : a ≠ 0 := by
    intro hz
    have heq := comp_one_add_X_twice p
    change a.comp (1 + X) = p at heq
    rw [hz, zero_comp] at heq
    exact hp0 heq.symm
  let r := a.natTrailingDegree
  have hr : r < 2 ^ s := a.natTrailingDegree_le_natDegree.trans_lt ha
  have har : a.coeff r ≠ 0 := coeff_natTrailingDegree_ne_zero.mpr ha0
  have hbefore : ∀ i < r, a.coeff i = 0 := fun _ hi =>
    coeff_eq_zero_of_lt_natTrailingDegree hi
  have hhist := pascal_history_weight_ge s a.coeff r hr har hbefore
  convert hhist using 1
  apply sum_congr rfl
  intro t ht
  let b := (X : (ZMod 2)[X]) ^ t * a
  have hb : b.natDegree < 2 ^ (s + 1) := by
    apply lt_of_le_of_lt (natDegree_mul_le) ?_
    rw [natDegree_X_pow, pow_succ]
    have := mem_range.mp ht
    omega
  have hcomb : principalCombination (s + 1) b.coeff = p * (1 + X) ^ t := by
    rw [principalCombination_coeff_eq_comp _ _ hb]
    change ((X : (ZMod 2)[X]) ^ t * p.comp (1 + X)).comp (1 + X) = _
    rw [mul_comp, X_pow_comp, comp_one_add_X_twice, mul_comm]
  rw [← hcomb, principalCombination_weight]
  apply intervalWeight_congr
  intro i hi
  congr 1
  funext j
  exact coeff_X_pow_mul' a t j

end Quantum.Stabilizer.Homological.BB.Fractal

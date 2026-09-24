import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Polynomial
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Dyadic decompositions of truncated Pascal rows

Polynomial coefficient windows of a binary Pascal row are sums of at most
`s` shifted full Pascal rows when the row length is bounded by `2^s`.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Polynomial
open scoped BigOperators

/-- The binary Pascal polynomial. -/
noncomputable def pascalPolynomial (t : ℕ) : (ZMod 2)[X] := (1 + X) ^ t

/-- The coefficient prefix of a polynomial, with an exclusive cutoff. -/
noncomputable def coefficientPrefix (p : (ZMod 2)[X]) (k : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range k, monomial i (p.coeff i)

/-- One coordinate functional of the open Pascal history. -/
noncomputable def historyFunctional (s t r : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range (width s),
    monomial i (if i ≤ r then (Nat.choose t (r - i) : ZMod 2) else 0)

/-- Prefix truncation keeps exactly the coefficients below its cutoff. -/
@[simp] lemma coefficientPrefix_coeff (p : (ZMod 2)[X]) (k i : ℕ) :
    (coefficientPrefix p k).coeff i = if i < k then p.coeff i else 0 := by
  classical
  simp [coefficientPrefix, coeff_monomial]

/-- The prefix with zero cutoff is zero. -/
@[simp] lemma coefficientPrefix_zero (p : (ZMod 2)[X]) :
    coefficientPrefix p 0 = 0 := by
  simp [coefficientPrefix]

/-- Prefix truncation is additive. -/
lemma coefficientPrefix_add (p q : (ZMod 2)[X]) (k : ℕ) :
    coefficientPrefix (p + q) k = coefficientPrefix p k + coefficientPrefix q k := by
  ext i
  simp only [coefficientPrefix_coeff, coeff_add]
  split_ifs <;> simp

/-- A cutoff beyond the support leaves a polynomial unchanged. -/
lemma coefficientPrefix_eq_self (p : (ZMod 2)[X]) (k : ℕ)
    (hp : ∀ i, k ≤ i → p.coeff i = 0) : coefficientPrefix p k = p := by
  ext i
  by_cases hi : i < k
  · simp [hi]
  · simp [hi, hp i (by omega)]

/-- Binary Pascal coefficients are binomial coefficients modulo two. -/
@[simp] lemma pascalPolynomial_coeff (t i : ℕ) :
    (pascalPolynomial t).coeff i = (Nat.choose t i : ZMod 2) := by
  exact coeff_one_add_X_pow (ZMod 2) t i

/-- A full Pascal row fits in every prefix longer than its degree. -/
lemma coefficientPrefix_pascal_eq (t k : ℕ) (ht : t < k) :
    coefficientPrefix (pascalPolynomial t) k = pascalPolynomial t := by
  apply coefficientPrefix_eq_self
  intro i hi
  simp [Nat.choose_eq_zero_of_lt (by omega : t < i)]

/-- A monomial shift starting beyond a prefix contributes nothing. -/
lemma coefficientPrefix_X_pow_mul_zero (p : (ZMod 2)[X]) (h k : ℕ) (hk : k ≤ h) :
    coefficientPrefix (X ^ h * p) k = 0 := by
  ext i
  simp only [coefficientPrefix_coeff, coeff_X_pow_mul', coeff_zero]
  by_cases hi : i < k
  · simp [hi, show ¬h ≤ i by omega]
  · simp [hi]

/-- Moving a monomial through a sufficiently long prefix shifts its cutoff. -/
lemma coefficientPrefix_X_pow_mul (p : (ZMod 2)[X]) (h k : ℕ) (hk : h ≤ k) :
    coefficientPrefix (X ^ h * p) k = X ^ h * coefficientPrefix p (k - h) := by
  ext i
  simp only [coefficientPrefix_coeff, coeff_X_pow_mul']
  split_ifs <;> simp_all <;> omega

/-- Splitting off the top bit splits a Pascal row into two disjoint translates. -/
lemma pascalPolynomial_width_add (s t : ℕ) :
    pascalPolynomial (width s + t) =
      pascalPolynomial t + X ^ width s * pascalPolynomial t := by
  unfold pascalPolynomial width
  rw [pow_add, add_pow_char_pow, one_pow, add_mul, one_mul]

/-- Sum the shifted full Pascal rows described by a list of exponent pairs. -/
noncomputable def pascalBlockSum (blocks : List (ℕ × ℕ)) : (ZMod 2)[X] :=
  (blocks.map fun b => X ^ b.1 * pascalPolynomial b.2).sum

/-- Translate every polynomial in a list of Pascal blocks. -/
def shiftPascalBlocks (h : ℕ) (blocks : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  blocks.map fun b => (h + b.1, b.2)

/-- Translating the block exponents multiplies their sum by a monomial. -/
lemma pascalBlockSum_shift (h : ℕ) (blocks : List (ℕ × ℕ)) :
    pascalBlockSum (shiftPascalBlocks h blocks) = X ^ h * pascalBlockSum blocks := by
  induction blocks with
  | nil => simp [pascalBlockSum, shiftPascalBlocks]
  | cons b blocks ih =>
    change X ^ (h + b.1) * pascalPolynomial b.2 +
        pascalBlockSum (shiftPascalBlocks h blocks) =
      X ^ h * (X ^ b.1 * pascalPolynomial b.2 + pascalBlockSum blocks)
    rw [ih, pow_add, mul_add, mul_assoc]

/-- A proper prefix of a Pascal row has a dyadic decomposition with at most
one block per bit. Each individual block is supported strictly below the cutoff. -/
theorem coefficientPrefix_pascal_decomposition (s t k : ℕ)
    (ht : t < width s) (hk : k < width s) :
    ∃ blocks : List (ℕ × ℕ), blocks.length ≤ s ∧
      (∀ b ∈ blocks, b.1 + b.2 < k) ∧
      coefficientPrefix (pascalPolynomial t) k = pascalBlockSum blocks := by
  induction s generalizing t k with
  | zero =>
    have hk0 : k = 0 := by simpa [width] using hk
    subst k
    exact ⟨[], by simp, by simp, by simp [pascalBlockSum]⟩
  | succ s ih =>
    have hw : width (s + 1) = width s * 2 := by simp [width, pow_succ]
    rw [hw] at ht hk
    by_cases hth : t < width s
    · by_cases hkh : k < width s
      · obtain ⟨blocks, hlen, hsupport, hsum⟩ := ih t k hth hkh
        exact ⟨blocks, by omega, hsupport, hsum⟩
      · refine ⟨[(0, t)], by simp, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_singleton] at hb
          subst b
          omega
        · rw [coefficientPrefix_pascal_eq t k (by omega)]
          simp [pascalBlockSum]
    · have htl : t - width s < width s := by omega
      have hte : t = width s + (t - width s) := by omega
      by_cases hkh : k < width s
      · obtain ⟨blocks, hlen, hsupport, hsum⟩ := ih (t - width s) k htl hkh
        refine ⟨blocks, by omega, hsupport, ?_⟩
        rw [hte, pascalPolynomial_width_add, coefficientPrefix_add,
          coefficientPrefix_X_pow_mul_zero _ _ _ (by omega), add_zero]
        exact hsum
      · have hkl : k - width s < width s := by omega
        obtain ⟨blocks, hlen, hsupport, hsum⟩ :=
          ih (t - width s) (k - width s) htl hkl
        refine ⟨(0, t - width s) :: shiftPascalBlocks (width s) blocks, ?_, ?_, ?_⟩
        · simpa [shiftPascalBlocks] using Nat.succ_le_succ hlen
        · intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            omega
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
            have hcdeg := hsupport c hc
            dsimp
            omega
        · rw [hte, pascalPolynomial_width_add, coefficientPrefix_add,
            coefficientPrefix_pascal_eq _ k (by omega),
            coefficientPrefix_X_pow_mul _ _ _ (by omega), hsum]
          simp only [Nat.add_sub_cancel_left]
          change pascalPolynomial (t - width s) + X ^ width s * pascalBlockSum blocks =
            X ^ 0 * pascalPolynomial (t - width s) +
              pascalBlockSum (shiftPascalBlocks (width s) blocks)
          rw [pascalBlockSum_shift]
          simp

/-- The same decomposition includes the full-width cutoff at positive indices. -/
theorem coefficientPrefix_pascal_decomposition_le (s t k : ℕ) (hs : 0 < s)
    (ht : t < width s) (hk : k ≤ width s) :
    ∃ blocks : List (ℕ × ℕ), blocks.length ≤ s ∧
      (∀ b ∈ blocks, b.1 + b.2 < k) ∧
      coefficientPrefix (pascalPolynomial t) k = pascalBlockSum blocks := by
  rcases lt_or_eq_of_le hk with hk | rfl
  · exact coefficientPrefix_pascal_decomposition s t k ht hk
  · refine ⟨[(0, t)], by simp; omega, ?_, ?_⟩
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      simpa using ht
    · rw [coefficientPrefix_pascal_eq _ _ ht]
      simp [pascalBlockSum]

/-- The coefficient description of an open-history coordinate functional. -/
@[simp] lemma historyFunctional_coeff (s t r i : ℕ) :
    (historyFunctional s t r).coeff i =
      if i < width s then
        if i ≤ r then (Nat.choose t (r - i) : ZMod 2) else 0
      else 0 := by
  classical
  simp [historyFunctional, coeff_monomial]

/-- Reflecting a shifted full Pascal row gives another such row. -/
lemma reflect_pascalBlock (r e u : ℕ) (heu : e + u ≤ r) :
    reflect r (X ^ e * pascalPolynomial u) =
      X ^ (r - e - u) * pascalPolynomial u := by
  ext i
  simp only [coeff_reflect, coeff_X_pow_mul', pascalPolynomial_coeff]
  by_cases hir : i ≤ r
  · rw [revAt_le hir]
    by_cases he : e ≤ r - i
    · by_cases hl : r - e - u ≤ i
      · simp only [he, hl, if_true]
        congr 1
        exact Nat.choose_symm_of_eq_add (by omega : u = (r - i - e) + (i - (r - e - u)))
      · simp [he, hl, Nat.choose_eq_zero_of_lt (by omega : u < r - i - e)]
    · have hl : r - e - u ≤ i := by omega
      simp [he, hl, Nat.choose_eq_zero_of_lt (by omega : u < i - (r - e - u))]
  · rw [revAt_eq_self_of_lt (by omega)]
    have he : e ≤ i := by omega
    have hl : r - e - u ≤ i := by omega
    simp [he, hl, Nat.choose_eq_zero_of_lt (by omega : u < i - e),
      Nat.choose_eq_zero_of_lt (by omega : u < i - (r - e - u))]

/-- A history coordinate before the recurrence width is a reflected Pascal prefix. -/
lemma historyFunctional_eq_reflect_prefix (s t r : ℕ) (hr : r < width s) :
    historyFunctional s t r = reflect r (coefficientPrefix (pascalPolynomial t) (r + 1)) := by
  ext i
  simp only [historyFunctional_coeff, coeff_reflect, coefficientPrefix_coeff,
    pascalPolynomial_coeff]
  by_cases hir : i ≤ r
  · rw [revAt_le hir]
    simp [hir, show i < width s by omega, show r - i < r + 1 by omega]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [hir, show ¬i < r + 1 by omega]

/-- A history coordinate beyond the Pascal degree is a shifted Pascal prefix. -/
lemma historyFunctional_eq_shift_prefix (s t r : ℕ) (htr : t ≤ r) :
    historyFunctional s t r =
      X ^ (r - t) * coefficientPrefix (pascalPolynomial t) (width s - (r - t)) := by
  ext i
  simp only [historyFunctional_coeff, coeff_X_pow_mul', coefficientPrefix_coeff,
    pascalPolynomial_coeff]
  by_cases hiq : i < width s
  · by_cases hli : r - t ≤ i
    · have hcut : i - (r - t) < width s - (r - t) := by omega
      simp only [hiq, hli, hcut, if_true]
      by_cases hir : i ≤ r
      · simp only [hir, if_true]
        congr 1
        exact Nat.choose_symm_of_eq_add (by omega : t = (r - i) + (i - (r - t)))
      · simp [hir, Nat.choose_eq_zero_of_lt (by omega : t < i - (r - t))]
    · have hir : i ≤ r := by omega
      simp [hiq, hli, hir, Nat.choose_eq_zero_of_lt (by omega : t < r - i)]
  · by_cases hli : r - t ≤ i
    · simp [hiq, hli, show ¬i - (r - t) < width s - (r - t) by omega]
    · simp [hiq, hli]

/-- Reflect each full Pascal block about a common coordinate. -/
def reflectPascalBlocks (r : ℕ) (blocks : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  blocks.map fun b => (r - b.1 - b.2, b.2)

/-- Reflection distributes over a list of Pascal blocks supported below its center. -/
lemma reflect_pascalBlockSum (r : ℕ) (blocks : List (ℕ × ℕ))
    (hblocks : ∀ b ∈ blocks, b.1 + b.2 ≤ r) :
    reflect r (pascalBlockSum blocks) = pascalBlockSum (reflectPascalBlocks r blocks) := by
  induction blocks with
  | nil => simp [pascalBlockSum, reflectPascalBlocks]
  | cons b blocks ih =>
    change reflect r (X ^ b.1 * pascalPolynomial b.2 + pascalBlockSum blocks) =
      X ^ (r - b.1 - b.2) * pascalPolynomial b.2 +
        pascalBlockSum (reflectPascalBlocks r blocks)
    rw [reflect_add, reflect_pascalBlock r b.1 b.2 (hblocks b (by simp)),
      ih (fun c hc => hblocks c (by simp [hc]))]

/-- Every coordinate functional of a width-`2^s` Pascal history is a sum of at most
`s` full shifted Pascal rows. No cyclic-distance hypothesis occurs in this theorem. -/
theorem historyFunctional_decomposition (s t r : ℕ) (hs : 0 < s)
    (ht : t < width s) :
    ∃ blocks : List (ℕ × ℕ), blocks.length ≤ s ∧
      (∀ b ∈ blocks, b.1 + b.2 < width s) ∧
      historyFunctional s t r = pascalBlockSum blocks := by
  by_cases hr : r < width s
  · obtain ⟨blocks, hlen, hsupport, hsum⟩ :=
      coefficientPrefix_pascal_decomposition_le s t (r + 1) hs ht (by omega)
    refine ⟨reflectPascalBlocks r blocks, ?_, ?_, ?_⟩
    · simpa [reflectPascalBlocks] using hlen
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      have hdeg := hsupport c hc
      dsimp
      omega
    · rw [historyFunctional_eq_reflect_prefix s t r hr, hsum,
        reflect_pascalBlockSum r blocks (fun b hb => by have := hsupport b hb; omega)]
  · obtain ⟨blocks, hlen, hsupport, hsum⟩ :=
      coefficientPrefix_pascal_decomposition_le s t (width s - (r - t)) hs ht (by omega)
    refine ⟨shiftPascalBlocks (r - t) blocks, ?_, ?_, ?_⟩
    · simpa [shiftPascalBlocks] using hlen
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      have hdeg := hsupport c hc
      dsimp
      omega
    · rw [historyFunctional_eq_shift_prefix s t r (by omega), hsum,
        pascalBlockSum_shift]

/-- A ring homomorphism satisfying the fractal recurrence turns each full Pascal
block into a single coordinate monomial. -/
theorem historyFunctional_map_eq_sum_powers {R : Type*} [Semiring R]
    (φ : (ZMod 2)[X] →+* R) (s t r : ℕ) (hs : 0 < s) (ht : t < width s)
    (hφ : φ (1 + X) = φ X ^ width s) :
    ∃ exponents : List ℕ, exponents.length ≤ s ∧
      φ (historyFunctional s t r) = (exponents.map fun e => φ X ^ e).sum := by
  obtain ⟨blocks, hlen, hsupport, hsum⟩ := historyFunctional_decomposition s t r hs ht
  refine ⟨blocks.map (fun b => b.1 + width s * b.2), by simpa using hlen, ?_⟩
  rw [hsum]
  clear hlen hsupport hsum
  have hblock (b : ℕ × ℕ) :
      φ (X ^ b.1 * pascalPolynomial b.2) = φ X ^ (b.1 + width s * b.2) := by
    rw [map_mul, map_pow, pascalPolynomial, map_pow, hφ, ← pow_mul, ← pow_add]
  induction blocks with
  | nil => simp [pascalBlockSum]
  | cons b blocks ih =>
    change φ (X ^ b.1 * pascalPolynomial b.2 + pascalBlockSum blocks) =
      φ X ^ (b.1 + width s * b.2) +
        ((blocks.map (fun c => c.1 + width s * c.2)).map fun e => φ X ^ e).sum
    rw [map_add, hblock, ih]

end Quantum.Stabilizer.Homological.BB.Fractal

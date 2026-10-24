import QEC.Stabilizer.Framework.Homological.F2Mask

namespace PackedSwap

/-- Flip a single binary coordinate using its arithmetic increment or decrement. -/
theorem xor_two_pow (i p : Nat) :
    i ^^^ 2 ^ p = if i.testBit p then i - 2 ^ p else i + 2 ^ p := by
  induction p generalizing i with
  | zero =>
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · simp [Nat.testBit_zero, h, Nat.xor_one_of_even (Nat.even_iff.mpr h)]
    · simp [Nat.testBit_zero, h, Nat.xor_one_of_odd (Nat.odd_iff.mpr h)]
  | succ p ih =>
    have hpow : 2 ^ (p + 1) = Nat.bit false (2 ^ p) := by
      simp [Nat.bit, pow_succ, Nat.mul_comm]
    conv_lhs => rw [← Nat.bit_bodd_div2 i, hpow, Nat.xor_bit]
    rw [ih, Nat.testBit_succ, ← Nat.div2_val]
    have heq := Nat.bit_bodd_div2 i
    by_cases hp : (Nat.div2 i).testBit p = true
    · have hle : 2 ^ p ≤ Nat.div2 i := by
        by_contra h
        have hx := Nat.testBit_lt_two_pow (Nat.lt_of_not_ge h)
        simp [hp] at hx
      simp only [hp, Bool.bne_false, Bool.true_eq, ite_true]
      cases hb : Nat.bodd i <;> simp [hb, Nat.bit, pow_succ] at heq ⊢ <;> omega
    · have hp' : (Nat.div2 i).testBit p = false := by simpa using hp
      simp only [hp', Bool.bne_false, Bool.false_eq_true, ite_false]
      cases hb : Nat.bodd i <;> simp [hb, Nat.bit, pow_succ] at heq ⊢ <;> omega

/-- Interchange two binary coordinates of a natural number. -/
def swap (p q i : Nat) : Nat :=
  if i.testBit p == i.testBit q then i else i ^^^ 2 ^ p ^^^ 2 ^ q

/-- Bit-level semantics of a binary-coordinate interchange. -/
theorem testBit_swap (p q i j : Nat) (hpq : p ≠ q) :
    (swap p q i).testBit j = if j = p then i.testBit q else if j = q then i.testBit p else i.testBit j := by
  unfold swap
  by_cases hjp : j = p
  · subst j
    cases hbp : i.testBit p <;> cases hbq : i.testBit q <;>
      simp [hbp, hbq, Nat.testBit_xor, Nat.testBit_two_pow, hpq, Ne.symm hpq]
  · by_cases hjq : j = q
    · subst j
      cases hbp : i.testBit p <;> cases hbq : i.testBit q <;>
        simp [hbp, hbq, Nat.testBit_xor, Nat.testBit_two_pow, hpq, Ne.symm hpq]
    · split <;> simp [hjp, hjq, Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm hjp, Ne.symm hjq]

/-- Interchanging the same coordinates twice restores the original state. -/
theorem swap_involutive (p q i : Nat) (hpq : p ≠ q) : swap p q (swap p q i) = i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_swap _ _ _ _ hpq]
  by_cases hjp : j = p <;> by_cases hjq : j = q <;> simp_all

/-- Swapping two coordinates inside a fixed bit width preserves that width. -/
theorem swap_lt (p q width i : Nat) (hp : p < width) (hq : q < width) (hi : i < 2 ^ width) :
    swap p q i < 2 ^ width := by
  unfold swap
  split
  · exact hi
  · exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hi
      (Nat.pow_lt_pow_right (by omega) hp)) (Nat.pow_lt_pow_right (by omega) hq)

/-- A set bit supplies its corresponding power-of-two lower bound. -/
theorem two_pow_le_of_testBit {i p : Nat} (h : i.testBit p = true) : 2 ^ p ≤ i := by
  by_contra hn
  have hz := Nat.testBit_lt_two_pow (Nat.lt_of_not_ge hn)
  simp [h] at hz

/-- Select the states whose low chosen bit moves to the higher chosen bit. -/
def up (p q i : Nat) : Bool := i.testBit p && !(i.testBit q)

/-- Select the states whose high chosen bit moves to the lower chosen bit. -/
def down (p q i : Nat) : Bool := !(i.testBit p) && i.testBit q

/-- The two moving subsets are disjoint. -/
theorem up_down_disjoint (p q i : Nat) : (up p q i && down p q i) = false := by
  unfold up down
  cases i.testBit p <;> cases i.testBit q <;> rfl

/-- A coordinate interchange exchanges the two moving subsets. -/
theorem up_swap (p q i : Nat) (hpq : p ≠ q) : up p q (swap p q i) = down p q i := by
  simp [up, down, testBit_swap _ _ _ _ hpq, hpq, Ne.symm hpq, Bool.and_comm]

/-- A coordinate interchange exchanges the two moving subsets in both directions. -/
theorem down_swap (p q i : Nat) (hpq : p ≠ q) : down p q (swap p q i) = up p q i := by
  simp [up, down, testBit_swap _ _ _ _ hpq, hpq, Ne.symm hpq, Bool.and_comm]

/-- The coordinate interchange is a fixed displacement on each moving subset. -/
theorem swap_eq_arithmetic (p q i : Nat) (hpq : p < q) :
    swap p q i = if up p q i then i + (2 ^ q - 2 ^ p)
      else if down p q i then i - (2 ^ q - 2 ^ p) else i := by
  have hne : p ≠ q := Nat.ne_of_lt hpq
  have hp : 2 ^ p ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
  cases hbp : i.testBit p <;> cases hbq : i.testBit q
  · simp [swap, up, down, hbp, hbq]
  · have hqi := two_pow_le_of_testBit hbq
    simp only [swap, up, down, hbp, hbq]
    change (i ^^^ 2 ^ p) ^^^ 2 ^ q = i - (2 ^ q - 2 ^ p)
    rw [xor_two_pow (i ^^^ 2 ^ p) q]
    simp only [Nat.testBit_xor, Nat.testBit_two_pow, hne, decide_false, Bool.bne_false, hbq]
    rw [xor_two_pow i p]
    simp only [hbp, Bool.false_eq_true, ite_false, ite_true]
    omega
  · have hpi := two_pow_le_of_testBit hbp
    simp only [swap, up, down, hbp, hbq]
    change (i ^^^ 2 ^ p) ^^^ 2 ^ q = i + (2 ^ q - 2 ^ p)
    rw [xor_two_pow (i ^^^ 2 ^ p) q]
    simp only [Nat.testBit_xor, Nat.testBit_two_pow, hne, decide_false, Bool.bne_false, hbq]
    rw [xor_two_pow i p]
    simp only [hbp, Bool.false_eq_true, ite_false, ite_true]
    omega
  · simp [swap, up, down, hbp, hbq]

/-- A state's highest allowed bit is set exactly when the state lies in the upper half. -/
theorem top_testBit (q i : Nat) (hi : i < 2 ^ (q + 1)) : i.testBit q = decide (2 ^ q ≤ i) := by
  by_cases h : 2 ^ q ≤ i
  · simpa [h] using Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h hi
  · have hlt : i < 2 ^ q := by omega
    simp [h, Nat.testBit_lt_two_pow hlt]

/-- Swap-and-delete in its explicit linear bit-mask form. -/
def forgetBit (position width state : Nat) : Nat :=
  if position + 1 < width then
    ((state &&& (2 ^ position - 1)) ^^^
      (state &&& ((2 ^ (width - 1) - 1) ^^^ (2 ^ (position + 1) - 1)))) ^^^
      (((state >>> (width - 1)) &&& 1) <<< position)
  else state &&& (2 ^ (width - 1) - 1)

/-- The only set binary coordinate of one is coordinate zero. -/
theorem testBit_one (j : Nat) : (1 : Nat).testBit j = decide (j = 0) := by
  apply Bool.coe_iff_coe.mp
  simp [Nat.testBit_one_eq_true_iff_self_eq_zero]

/-- The linear bit-mask deletion is the lower half of the corresponding swap. -/
theorem forgetBit_eq_swap_mod (p q i : Nat) (hpq : p < q) :
    forgetBit p (q + 1) i = swap p q i % 2 ^ q := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hpw : p + 1 < q + 1 := by omega
  have hne : p ≠ q := Nat.ne_of_lt hpq
  simp only [forgetBit, hpw, ite_true, Nat.add_sub_cancel,
    Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, testBit_one,
    Nat.testBit_mod_two_pow, testBit_swap _ _ _ _ hne]
  by_cases hjp : j = p
  · subst j
    simp [hpq]
  · by_cases hjq : j < q
    · by_cases hj : j < p
      · have : ¬ p ≤ j := by omega
        simp [hjp, hjq, hj, this, show j < p + 1 by omega, show j ≠ q by omega]
      · have hjgt : p < j := by omega
        have hsub : j - p ≠ 0 := by omega
        simp [hjp, hjq, hj, hsub, show ¬ j < p + 1 by omega, show j ≠ q by omega]
    · have hjgt : p < j := by omega
      have hsub : j - p ≠ 0 := by omega
      simp [hjp, hjq, hsub, show ¬ j < p by omega, show ¬ j < p + 1 by omega]

/-- The downward-moving states are exactly those receiving the upward-shifted lanes. -/
theorem lowIncoming_eq_down (p q i : Nat) (hpq : p < q) (hi : i < 2 ^ (q + 1)) :
    (decide (2 ^ q - 2 ^ p ≤ i) && decide (i - (2 ^ q - 2 ^ p) < 2 ^ (q + 1)) &&
      up p q (i - (2 ^ q - 2 ^ p))) = down p q i := by
  apply Bool.coe_iff_coe.mp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hd, hr⟩, hu⟩
    have hs := swap_eq_arithmetic p q (i - (2 ^ q - 2 ^ p)) hpq
    have hx := down_swap p q (i - (2 ^ q - 2 ^ p)) (Nat.ne_of_lt hpq)
    simp only [hu, ite_true] at hs
    rw [hs, Nat.sub_add_cancel hd] at hx
    exact hx.trans hu
  · intro hd
    have hbq : i.testBit q = true := (Bool.and_eq_true_iff.mp hd).2
    have hle := two_pow_le_of_testBit hbq
    have hu : up p q i = false := by
      have hdis := up_down_disjoint p q i
      simpa [hd] using hdis
    have hs := swap_eq_arithmetic p q i hpq
    simp only [hu, hd, Bool.false_eq_true, ite_false, ite_true] at hs
    have hr := swap_lt p q (q + 1) i (by omega) (by omega) hi
    rw [hs] at hr
    have hx := up_swap p q i (Nat.ne_of_lt hpq)
    rw [hs, hd] at hx
    exact ⟨⟨(Nat.sub_le _ _).trans hle, hr⟩, hx⟩

/-- The upward-moving states are exactly those receiving the downward-shifted lanes. -/
theorem highIncoming_eq_up (p q i : Nat) (hpq : p < q) (hi : i < 2 ^ (q + 1)) :
    (decide (i + (2 ^ q - 2 ^ p) < 2 ^ (q + 1)) &&
      down p q (i + (2 ^ q - 2 ^ p))) = up p q i := by
  apply Bool.coe_iff_coe.mp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, hd⟩
    have hu : up p q (i + (2 ^ q - 2 ^ p)) = false := by
      have hdis := up_down_disjoint p q (i + (2 ^ q - 2 ^ p))
      simpa [hd] using hdis
    have hs := swap_eq_arithmetic p q (i + (2 ^ q - 2 ^ p)) hpq
    simp only [hu, hd, Bool.false_eq_true, ite_false, ite_true, Nat.add_sub_cancel] at hs
    have hx := up_swap p q (i + (2 ^ q - 2 ^ p)) (Nat.ne_of_lt hpq)
    rw [hs, hd] at hx
    exact hx
  · intro hu
    have hs := swap_eq_arithmetic p q i hpq
    simp only [hu, ite_true] at hs
    have hr := swap_lt p q (q + 1) i (by omega) (by omega) hi
    rw [hs] at hr
    have hx := down_swap p q i (Nat.ne_of_lt hpq)
    rw [hs, hu] at hx
    exact ⟨hr, hx⟩

#print axioms lowIncoming_eq_down
#print axioms highIncoming_eq_up
#print axioms swap_eq_arithmetic
#print axioms forgetBit_eq_swap_mod
#print axioms xor_two_pow
#print axioms testBit_swap
#print axioms swap_involutive
end PackedSwap

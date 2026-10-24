import QEC.Stabilizer.Framework.Homological.BZCertificate

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Clearing the least set bit removes at most one bit from any finite prefix. -/
theorem bitCount_le_clear_add_one (n x : Nat) :
    bitCount n x ≤ bitCount n (x &&& (x-1)) + 1 := by
  induction n generalizing x with
  | zero => simp [bitCount]
  | succ n ih =>
    by_cases hx : x = 0
    · subst x
      simp only [Nat.zero_and, bitCount]
      omega
    have hmod : (x &&& (x-1)) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (x &&& (x-1)) with h | h
      · exact h
      · have h' := Nat.and_mod_two_eq_one.mp h
        omega
    rw [bitCount, bitCount, hmod, Nat.zero_add, Nat.and_div_two]
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · have hdiv : (x-1)/2 = x/2-1 := by omega
      rw [hdiv, he, Nat.zero_add]
      exact ih (x/2)
    · have hdiv : (x-1)/2 = x/2 := by omega
      rw [hdiv, Nat.and_self, ho]
      omega

/-- A sparse bit counter uses a safe upper bound if its finite fuel is exhausted. -/
def sparsePopBound (bits : Nat) : Nat → Nat → Nat
  | 0, x => if Nat.beq x 0 then 0 else bits
  | k+1, x => if Nat.beq x 0 then 0 else
      Nat.add 1 (sparsePopBound bits k (Nat.land x (Nat.sub x 1)))

/-- The sparse counter always bounds the actual number of bits, including on exhaustion. -/
theorem bitCount_le_sparsePopBound (bits fuel x : Nat) :
    bitCount bits x ≤ sparsePopBound bits fuel x := by
  induction fuel generalizing x with
  | zero =>
    by_cases hx : x = 0
    · subst x
      simp [sparsePopBound, bitCount_eq_card]
    · simp only [sparsePopBound, Nat.beq_eq, hx, if_false]
      rw [bitCount_eq_card]
      exact le_trans (Finset.card_filter_le _ _) (by simp)
  | succ k ih =>
    by_cases hx : x = 0
    · subst x
      simp [sparsePopBound, bitCount_eq_card]
    · simp only [sparsePopBound, Nat.beq_eq, hx, if_false]
      have hp := bitCount_le_clear_add_one bits x
      have hi := ih (x &&& (x-1))
      change bitCount bits x ≤ 1 + sparsePopBound bits k (x &&& (x-1))
      omega

#print axioms bitCount_le_sparsePopBound
end Quantum.Stabilizer.Homological.F2Mask

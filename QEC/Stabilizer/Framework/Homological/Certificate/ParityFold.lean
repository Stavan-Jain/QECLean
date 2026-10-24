import QEC.Stabilizer.Framework.Homological.BZCertificate
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Parity of a packed XOR is the sum of the two parities. -/
theorem bitCount_xor_mod_two (n a b : ℕ) :
    bitCount n (a ^^^ b) % 2 = (bitCount n a + bitCount n b) % 2 := by
  induction n generalizing a b with
  | zero => simp [bitCount]
  | succ n ih =>
    have hd : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 := by
      simpa [Nat.shiftRight_eq_div_pow] using
        (Nat.shiftRight_xor_distrib (a := a) (b := b) (i := 1))
    simp only [bitCount, hd]
    rw [Nat.xor_mod_two_eq]
    have hi := ih (a / 2) (b / 2)
    omega

/-- Fold a power-of-two block down to its parity using logarithmically many XORs. -/
def parityFold : ℕ → ℕ → ℕ
  | 0, x => x % 2
  | k + 1, x => parityFold k (Nat.xor x (Nat.shiftRight x (2 ^ k)))

/-- The logarithmic XOR fold computes the parity of the low `2^k` bits. -/
theorem parityFold_eq (k x : ℕ) : parityFold k x = bitCount (2 ^ k) x % 2 := by
  induction k generalizing x with
  | zero => simp [parityFold, bitCount]
  | succ k ih =>
    rw [parityFold, ih]
    change bitCount (2 ^ k) (x ^^^ (x >>> (2 ^ k))) % 2 = _
    rw [bitCount_xor_mod_two, pow_succ, Nat.mul_two, bitCount_add]
    rw [Nat.shiftRight_eq_div_pow]

/-- Packed intersection counts compute the binary dot product. -/
theorem bitCount_land_eq_dot (n a b : ℕ) :
    (bitCount n (a &&& b) : ZMod 2) =
      ∑ i : Fin n, (if a.testBit i then (1 : ZMod 2) else 0) *
        (if b.testBit i then (1 : ZMod 2) else 0) := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
    rw [bitCount_succ, Nat.cast_add, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    congr 1
    simp only [Nat.testBit_and]
    have h : ∀ x y : Bool, ((if x && y then 1 else 0 : ℕ) : ZMod 2) =
        (if x then 1 else 0) * (if y then 1 else 0) := by decide
    exact h _ _

/-- The dot product with a fixed packed vector is an additive binary functional. -/
def dualOfMask (n mask : ℕ) : (Fin n → ZMod 2) →+ ZMod 2 where
  toFun v := ∑ i, chainOfMask (Equiv.refl (Fin n)) mask i * v i
  map_zero' := by simp
  map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]

/-- Evaluating the packed dual on a packed vector is intersection parity. -/
theorem dualOfMask_chainOfMask (n a b : ℕ) :
    dualOfMask n a (chainOfMask (Equiv.refl (Fin n)) b) =
      (bitCount n (a &&& b) : ZMod 2) := by
  simp only [dualOfMask, AddMonoidHom.coe_mk, ZeroHom.coe_mk, chainOfMask,
    Equiv.refl_apply]
  exact (bitCount_land_eq_dot n a b).symm

/-- The fast parity fold evaluates a binary dual on a power-of-two block. -/
theorem dualOfMask_eq_parityFold (k a b : ℕ) :
    dualOfMask (2 ^ k) a (chainOfMask (Equiv.refl (Fin (2 ^ k))) b) =
      (parityFold k (a &&& b) : ZMod 2) := by
  rw [dualOfMask_chainOfMask, parityFold_eq, ZMod.natCast_mod]

#print axioms dualOfMask_eq_parityFold

end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.F2Mask
/-- Extending a bit-count prefix past a bounded word adds no set bits. -/
theorem bitCount_extend (n m x : Nat) (hnm : n ≤ m) (hx : x < 2^n) :
    bitCount m x = bitCount n x := by
  rw [show m = n + (m-n) by omega, bitCount_add, Nat.div_eq_of_lt hx]
  simp [bitCount_eq_card]

/-- Equal binary dot products give equal fast parity folds on bounded words. -/
theorem parityFold_eq_of_cast_eq (n k a b : Nat) (hn : n ≤ 2^k)
    (ha : a < 2^n) (hb : b < 2^n)
    (h : (bitCount n a : ZMod 2) = (bitCount n b : ZMod 2)) :
    parityFold k a = parityFold k b := by
  rw [parityFold_eq, parityFold_eq, bitCount_extend n (2^k) a hn ha,
    bitCount_extend n (2^k) b hn hb]
  have hv := congrArg ZMod.val h
  simpa using hv

#print axioms parityFold_eq_of_cast_eq
end Quantum.Stabilizer.Homological.F2Mask

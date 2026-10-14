/-
# Packed-`Nat` encodings of `𝔽₂`-chains

Kernel `decide` over `𝔽₂`-chains is only fast when the chains are packed into
`Nat` bitmasks: XOR, shifts and masks are single GMP operations in the kernel,
while evaluating a `ZMod 2`-valued function point by point is not. This module
is the bridge, generic in the index type: an enumeration `e : ι ≃ Fin n` packs
a chain `x : ι → ZMod 2` into `maskOf e x`, with

* `maskOf_add` — addition of chains is XOR of masks;
* `card_support_eq_bitCount` — the Hamming weight is the bit count;
* `maskOf_chainOfMask` / `chainOfMask_maskOf` — the two directions invert.

`bitCount n m` (the number of set bits below `n`) is the specification, and
`bitCountFast` evaluates it a byte at a time from a packed `256`-entry table
(`bitCountFast_eq`), which is what certificates should put inside `decide`.
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Bits
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Quantum
namespace Stabilizer
namespace Homological
namespace F2Mask

/-! ## Bit counts -/

/-- The number of set bits of `m` among the positions `0, …, n − 1`. -/
def bitCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => m % 2 + bitCount n (m / 2)

lemma bitCount_add (a b m : ℕ) :
    bitCount (a + b) m = bitCount a m + bitCount b (m / 2 ^ a) := by
  induction a generalizing m with
  | zero => simp [bitCount]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, bitCount, bitCount, ih,
      Nat.div_div_eq_div_mul, ← pow_succ']
    omega

/-- The top step of a bit count. -/
lemma bitCount_succ (n m : ℕ) :
    bitCount (n + 1) m = bitCount n m + if m.testBit n then 1 else 0 := by
  rw [bitCount_add, show bitCount 1 (m / 2 ^ n) = m / 2 ^ n % 2 by simp [bitCount]]
  congr 1
  have h := Nat.testBit_div_two_pow (n := n) m 0
  rw [zero_add, Nat.testBit_zero] at h
  rw [← h]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with h2 | h2 <;> simp [h2]

/-- `bitCount` is the cardinality of the set of set bits below `n`. -/
lemma bitCount_eq_card (n m : ℕ) :
    bitCount n m = ((Finset.range n).filter (fun i => m.testBit i = true)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bitCount_succ, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

/-- Only the bits below `n` matter. -/
lemma bitCount_mod (n m : ℕ) : bitCount n (m % 2 ^ n) = bitCount n m := by
  rw [bitCount_eq_card, bitCount_eq_card]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  simp [Nat.testBit_mod_two_pow, Finset.mem_range.mp hi]

/-! ## A byte-table popcount for kernel evaluation

These are written with the raw `Nat.*` functions rather than `>>>`, `&&&`, `%`:
the kernel evaluates both with GMP, but the notation goes through typeclass
instances that the kernel re-unfolds at every call, which dominates the cost of
a long `decide` walk. -/

/-- `bitCount 8 y` for every byte `y`, packed four bits per entry (entry `y` at
bit `4·y`), assembled from four 64-digit pieces to respect the line limit. -/
def POP8 : ℕ :=
  Nat.lor (Nat.shiftLeft 0x8776766576656554766565546554544376656554655454436554544354434332 768) <|
  Nat.lor (Nat.shiftLeft 0x7665655465545443655454435443433265545443544343325443433243323221 512) <|
  Nat.lor (Nat.shiftLeft 0x7665655465545443655454435443433265545443544343325443433243323221 256)
    0x6554544354434332544343324332322154434332433232214332322132212110

/-- Popcount of the lowest byte, read from `POP8`. -/
def pop8 (m : ℕ) : ℕ := Nat.land (Nat.shiftRight POP8 (Nat.mul 4 (Nat.mod m 256))) 15

/-- Popcount of the lowest `k` bytes, one table lookup per byte. -/
def bitCountFast : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => Nat.add (pop8 m) (bitCountFast k (Nat.shiftRight m 8))

private lemma pop8_table : ∀ y < 256, pop8 y = bitCount 8 y := by decide +kernel

lemma pop8_eq (m : ℕ) : pop8 m = bitCount 8 m := by
  have h := pop8_table (m % 256) (Nat.mod_lt _ (by norm_num))
  have hm : pop8 (m % 256) = pop8 m := by
    unfold pop8
    rw [show Nat.mod (m % 256) 256 = Nat.mod m 256 from Nat.mod_mod m 256]
  rw [hm] at h
  rw [h, show (256 : ℕ) = 2 ^ 8 by norm_num, bitCount_mod]

/-- The byte-table popcount computes `bitCount` on the lowest `8·k` bits. -/
lemma bitCountFast_eq (k m : ℕ) : bitCountFast k m = bitCount (8 * k) m := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    change pop8 m + bitCountFast k (m >>> 8) = _
    rw [ih, pop8_eq, show 8 * (k + 1) = 8 + 8 * k by ring, bitCount_add,
      Nat.shiftRight_eq_div_pow]

/-! ## Masks of chains -/

/-- Bits `0, …, n − 1` read off a Boolean function. -/
def ofBits (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.bit (b 0) (ofBits (fun i => b (i + 1)) n)

lemma testBit_ofBits (b : ℕ → Bool) (n i : ℕ) :
    (ofBits b n).testBit i = (decide (i < n) && b i) := by
  induction n generalizing b i with
  | zero => simp [ofBits]
  | succ n ih =>
    cases i with
    | zero => simp [ofBits]
    | succ i => simp [ofBits, Nat.testBit_bit_succ, ih]

/-- XOR of a list of masks. -/
def xorList (l : List ℕ) : ℕ := l.foldr (· ^^^ ·) 0

@[simp] lemma xorList_nil : xorList [] = 0 := rfl

@[simp] lemma xorList_cons (a : ℕ) (l : List ℕ) : xorList (a :: l) = a ^^^ xorList l := rfl

variable {ι : Type*} {n : ℕ} (e : ι ≃ Fin n)

/-- The mask of a chain: bit `e i` is set iff `x i ≠ 0`. -/
def maskOf (x : ι → ZMod 2) : ℕ :=
  ofBits (fun k => if h : k < n then decide (x (e.symm ⟨k, h⟩) ≠ 0) else false) n

/-- The chain of a mask: `1` exactly at the indices whose bit is set. -/
def chainOfMask (M : ℕ) : ι → ZMod 2 := fun i => if M.testBit (e i) then 1 else 0

lemma testBit_maskOf (x : ι → ZMod 2) (k : ℕ) :
    (maskOf e x).testBit k
      = if h : k < n then decide (x (e.symm ⟨k, h⟩) ≠ 0) else false := by
  rw [maskOf, testBit_ofBits]
  by_cases h : k < n <;> simp [h]

@[simp] lemma testBit_maskOf_apply (x : ι → ZMod 2) (i : ι) :
    (maskOf e x).testBit (e i) = decide (x i ≠ 0) := by
  rw [testBit_maskOf, dif_pos (e i).isLt]
  simp

lemma maskOf_lt (x : ι → ZMod 2) : maskOf e x < 2 ^ n := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_maskOf, dif_neg (by omega)]

private lemma zmod2_add_ne (a b : ZMod 2) :
    decide (a + b ≠ 0) = (decide (a ≠ 0) ^^ decide (b ≠ 0)) := by
  revert a b; decide

private lemma zmod2_eq_ite (a : ZMod 2) : (if a ≠ 0 then (1 : ZMod 2) else 0) = a := by
  revert a; decide

/-- Addition of chains is XOR of masks. -/
lemma maskOf_add (x y : ι → ZMod 2) : maskOf e (x + y) = maskOf e x ^^^ maskOf e y := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [Nat.testBit_xor, testBit_maskOf, testBit_maskOf, testBit_maskOf]
  split_ifs
  · exact zmod2_add_ne _ _
  · rfl

@[simp] lemma maskOf_zero : maskOf e (0 : ι → ZMod 2) = 0 := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [testBit_maskOf, Nat.zero_testBit]
  split_ifs <;> simp

/-- Masks of a list sum are the XOR of the masks. -/
lemma maskOf_sum (l : List (ι → ZMod 2)) :
    maskOf e l.sum = xorList (l.map (maskOf e)) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, maskOf_add, ih, List.map_cons, xorList_cons]

lemma chainOfMask_maskOf (x : ι → ZMod 2) : chainOfMask e (maskOf e x) = x := by
  funext i
  simp only [chainOfMask, testBit_maskOf_apply, decide_eq_true_eq]
  exact zmod2_eq_ite _

lemma maskOf_injective : Function.Injective (maskOf e) := fun x y h => by
  rw [← chainOfMask_maskOf e x, h, chainOfMask_maskOf]

lemma maskOf_chainOfMask {M : ℕ} (hM : M < 2 ^ n) : maskOf e (chainOfMask e M) = M := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [testBit_maskOf]
  split_ifs with h
  · simp only [chainOfMask, Equiv.apply_symm_apply]
    split_ifs with hb <;> simp only [hb] <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]

/-- The Hamming weight of a chain is the bit count of its mask. -/
lemma card_support_eq_bitCount [Fintype ι] (x : ι → ZMod 2) :
    (Finset.univ.filter fun i => x i ≠ 0).card = bitCount n (maskOf e x) := by
  rw [bitCount_eq_card]
  refine Finset.card_bij (fun i _ => (e i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [Finset.mem_filter, hi]
  · intro i _ j _ h
    exact e.injective (Fin.ext h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk, hb⟩ := hk
    refine ⟨e.symm ⟨k, hk⟩, ?_, by simp⟩
    rw [testBit_maskOf, dif_pos hk] at hb
    simpa using hb

end F2Mask
end Homological
end Stabilizer
end Quantum

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Bits
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Packed-`Nat` encodings of `𝔽₂`-chains

Kernel `decide` over `𝔽₂`-chains is only fast when the chains are packed into
`Nat` bitmasks: XOR, shifts and masks are single big-number operations in the
kernel, while evaluating a `ZMod 2`-valued function point by point is not. This
module is the dictionary between the two, generic in the index type: an
enumeration `e : ι ≃ Fin n` packs a chain `x : ι → ZMod 2` into the mask
`maskOf e x`, and `chainOfMask e M` reads a mask back as a chain.

* `maskOf_add`, `maskOf_sum`, `chainOfMask_xor`: addition of chains is XOR of
  masks.
* `maskOf_chainOfMask`, `chainOfMask_maskOf`: the two directions invert each
  other (on masks below `2 ^ n`).
* `maskOf_single`, `chainOfMask_two_pow`: point masses are single bits.
* `card_support_eq_bitCount`: the Hamming weight of a chain is the bit count
  of its mask.

`bitCount n m`, the number of set bits of `m` below position `n`, is the
specification of the weight. `bitCountFast` evaluates it a byte at a time from
a packed `256`-entry table (`bitCountFast_eq`), and is the form to put inside a
`decide`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace F2Mask

/-! ## Bit counts -/

/-- The number of set bits of `m` among the positions `0, …, n − 1`. -/
def bitCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => m % 2 + bitCount n (m / 2)

/-- A bit count over `a + b` positions splits into the low `a` positions and
the next `b`. -/
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
  rw [bitCount_add, Nat.testBit_eq_decide_div_mod_eq]
  simp only [bitCount, Nat.add_zero, decide_eq_true_eq]
  split <;> omega

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

/-- There are at most `n` set bits below position `n`. -/
lemma bitCount_le (n m : ℕ) : bitCount n m ≤ n := by
  rw [bitCount_eq_card]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)

/-- The zero word has no set bits. -/
lemma bitCount_zero_right (n : ℕ) : bitCount n 0 = 0 := by
  simp [bitCount_eq_card]

/-- Counting over more positions than a word occupies does not change the
count. -/
lemma bitCount_extend (bits extra m : ℕ) (hm : m < 2 ^ bits) :
    bitCount (bits + extra) m = bitCount bits m := by
  rw [bitCount_add, Nat.div_eq_of_lt hm, bitCount_zero_right, Nat.add_zero]

/-! ## A byte-table popcount for kernel evaluation

These are written with the raw `Nat.*` functions rather than `>>>`, `&&&`, `%`:
the kernel evaluates both with big-number primitives, but the notation goes
through typeclass instances that the kernel re-unfolds at every call, which
dominates the cost of a long `decide` walk. -/

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

/-- The table lookup computes the bit count of the lowest byte. -/
lemma pop8_eq (m : ℕ) : pop8 m = bitCount 8 m := by
  rw [← bitCount_mod, ← pop8_table (m % 2 ^ 8) (Nat.mod_lt _ (by norm_num))]
  exact congrArg (fun k => Nat.land (Nat.shiftRight POP8 (Nat.mul 4 k)) 15)
    (Nat.mod_mod m 256).symm

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

/-- Bit `i` of `ofBits b n` is `b i` below `n` and `false` from `n` on. -/
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

/-- Bit `k` of the mask of `x` is set iff `k < n` and `x` is nonzero at the
index enumerated as `k`. -/
lemma testBit_maskOf (x : ι → ZMod 2) (k : ℕ) :
    (maskOf e x).testBit k
      = if h : k < n then decide (x (e.symm ⟨k, h⟩) ≠ 0) else false := by
  rw [maskOf, testBit_ofBits]
  by_cases h : k < n <;> simp [h]

/-- Bit `e i` of the mask of `x` is set iff `x i ≠ 0`. -/
@[simp] lemma testBit_maskOf_apply (x : ι → ZMod 2) (i : ι) :
    (maskOf e x).testBit (e i) = decide (x i ≠ 0) := by
  simp [testBit_maskOf]

/-- The mask of a chain on `n` indices occupies the lowest `n` bits. -/
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

/-- The mask of a list sum is the XOR of the masks. -/
lemma maskOf_sum (l : List (ι → ZMod 2)) :
    maskOf e l.sum = xorList (l.map (maskOf e)) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, maskOf_add, ih, List.map_cons, xorList_cons]

/-- Reading back the mask of a chain recovers the chain. -/
lemma chainOfMask_maskOf (x : ι → ZMod 2) : chainOfMask e (maskOf e x) = x := by
  funext i
  simp only [chainOfMask, testBit_maskOf_apply, decide_eq_true_eq]
  exact zmod2_eq_ite _

/-- Distinct chains have distinct masks. -/
lemma maskOf_injective : Function.Injective (maskOf e) := fun x y h => by
  rw [← chainOfMask_maskOf e x, h, chainOfMask_maskOf]

/-- A mask below `2 ^ n` is the mask of the chain it reads as. -/
lemma maskOf_chainOfMask {M : ℕ} (hM : M < 2 ^ n) : maskOf e (chainOfMask e M) = M := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [testBit_maskOf]
  split_ifs with h
  · simp only [chainOfMask, Equiv.apply_symm_apply]
    split_ifs with hb <;> simp only [hb] <;> decide
  · exact (Nat.testBit_lt_two_pow (hM.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

/-- The zero mask reads as the zero chain. -/
lemma chainOfMask_zero : chainOfMask e 0 = 0 := by
  ext i
  simp [chainOfMask]

/-- The XOR of two masks reads as the sum of their chains. -/
lemma chainOfMask_xor (a b : ℕ) :
    chainOfMask e (a ^^^ b) = chainOfMask e a + chainOfMask e b := by
  ext i
  simp only [chainOfMask, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit (e i) <;> cases b.testBit (e i) <;> decide

/-- The mask with only the bit of index `i` set reads as the point mass at
`i`. -/
lemma chainOfMask_two_pow [DecidableEq ι] (i : ι) :
    chainOfMask e (2 ^ (e i).val) = Pi.single i 1 := by
  funext k
  simp [chainOfMask, Nat.testBit_two_pow, Pi.single_apply, Fin.val_inj, eq_comm]

/-- The mask of the point mass at `i` has exactly the bit of index `i` set. -/
lemma maskOf_single [DecidableEq ι] (i : ι) :
    maskOf e (Pi.single i 1) = 2 ^ (e i).val := by
  rw [← chainOfMask_two_pow,
    maskOf_chainOfMask e (Nat.pow_lt_pow_right (by norm_num) (e i).isLt)]

/-- The Hamming weight of a chain is the bit count of its mask. -/
lemma card_support_eq_bitCount [Fintype ι] (x : ι → ZMod 2) :
    (Finset.univ.filter fun i => x i ≠ 0).card = bitCount n (maskOf e x) := by
  rw [bitCount_eq_card]
  refine Finset.card_bij (fun i _ => (e i : ℕ)) ?_ (fun i _ j _ h => e.injective (Fin.ext h)) ?_
  · intro i hi
    simpa using hi
  · intro k hk
    obtain ⟨hk, hb⟩ : k < n ∧ (maskOf e x).testBit k = true := by simpa using hk
    refine ⟨e.symm ⟨k, hk⟩, ?_, by simp⟩
    rw [testBit_maskOf, dif_pos hk] at hb
    simpa using hb

end F2Mask
end Homological
end Stabilizer
end Quantum

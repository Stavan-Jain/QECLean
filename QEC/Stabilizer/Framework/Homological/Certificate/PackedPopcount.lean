import QEC.Stabilizer.Framework.Homological.Certificate.PackedLaneShifts
import Mathlib.Tactic.FinCases

/-!
# Parallel popcounts on packed tables

The population count of every lane of a packed table is computed by a tree of
pair-summing stages: stage `k` adds adjacent blocks of `2 ^ k` bits, so after
`k` stages every block of `2 ^ k` bits holds the number of set bits it
originally contained.

* `popcountTree k size v` is the generic tree, and `popcountTree_eq` shows
  that it leaves `F2Mask.bitCount (2 ^ k)` of each block in that block;
  `popcountTree_packF` reads this off for a packed table of bounded entries.
* `popcount128` is the seven-stage operation on lanes of `128` bits, written
  with precomputed masks `popcountMask` for kernel evaluation;
  `popcount128_packF` shows that it returns the bit count of every entry
  below `2 ^ 90`.
-/

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-! ## The pair-summing tree -/

/-- Pair adjacent digits into double-width lanes. -/
lemma packF_pair (width size : Nat) (f : Nat → Nat) :
    packF width (2 * size) f =
      packF (2 * width) size (fun i => f (2 * i) + 2 ^ width * f (2 * i + 1)) := by
  induction size with
  | zero => simp [packF]
  | succ size ih =>
    rw [show 2 * (size + 1) = 2 * size + 1 + 1 by omega, packF_succ, packF_succ, ih, packF_succ]
    simp only [Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_assoc]
    ring

/-- Merging adjacent lanes sums their entries without carry into the next
pair. -/
lemma packed_pair_sum (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < 2 * size, f i < 2 ^ width) :
    let v := packF width (2 * size) f
    let mask := packF (2 * width) size (fun _ => 2 ^ width - 1)
    (v &&& mask) + ((v >>> width) &&& mask) =
      packF (2 * width) size (fun i => f (2 * i) + f (2 * i + 1)) := by
  dsimp only
  rw [packF_pair]
  let p := fun i => f (2 * i) + 2 ^ width * f (2 * i + 1)
  have hp : ∀ i < size, p i < 2 ^ (2 * width) := by
    intro i hi
    have ha := hf (2 * i) (by omega)
    have hb := hf (2 * i + 1) (by omega)
    dsimp [p]
    rw [show 2 * width = width + width by omega, pow_add]
    nlinarith [Nat.two_pow_pos width]
  have hm : 2 ^ width - 1 < 2 ^ (2 * width) :=
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.pow_le_pow_right Nat.two_pos (by omega))
  change (packF (2 * width) size p &&& _) + ((packF (2 * width) size p >>> width) &&& _) = _
  rw [packF_and (2 * width) size p _ (by omega) hp (fun _ _ => hm),
    masked_shiftRight_packF (2 * width) size width (2 ^ width - 1) p (by omega) hp hm]
  · rw [packF_add]
    refine packF_congr _ _ _ _ fun i hi => ?_
    have ha := hf (2 * i) (by omega)
    have hb := hf (2 * i + 1) (by omega)
    simp [p, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.add_mul_div_left, Nat.div_eq_of_lt ha]
  · intro j hj hge
    rw [Nat.testBit_two_pow_sub_one]
    simp [show ¬ j < width by omega]

/-- One-bit lanes are the bit counts of the corresponding input bits. -/
lemma packF_bitCount_one (size value : Nat) (hv : value < 2 ^ size) :
    value = packF 1 size (fun i => bitCount 1 (value >>> i)) := by
  refine eq_of_lane_eq Nat.one_pos fun i => ?_
  rw [lane_packF 1 size i _ (fun j _ => by have := bitCount_le 1 (value >>> j); omega),
    lane_eq_div_mod]
  simp only [Nat.one_mul, pow_one]
  by_cases hi : i < size
  · simp [hi, bitCount, Nat.shiftRight_eq_div_pow]
  · have hzero : value / 2 ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right Nat.two_pos (by omega)))
    simp [hi, hzero]

/-- Pair-summing stages compute all block popcounts in parallel: stage `k + 1`
adds the two halves of every block of `2 ^ (k + 1)` bits. -/
def popcountTree : Nat → Nat → Nat → Nat
  | 0, _, value => value
  | k + 1, size, value =>
    let prior := popcountTree k (2 * size) value
    let mask := packF (2 ^ (k + 1)) size (fun _ => 2 ^ (2 ^ k) - 1)
    (prior &&& mask) + ((prior >>> (2 ^ k)) &&& mask)

/-- The parallel tree produces the exact popcount in each power-of-two lane. -/
theorem popcountTree_eq (k size value : Nat) (hv : value < 2 ^ (2 ^ k * size)) :
    popcountTree k size value =
      packF (2 ^ k) size (fun i => bitCount (2 ^ k) (value >>> (2 ^ k * i))) := by
  induction k generalizing size with
  | zero => simpa [popcountTree] using packF_bitCount_one size value (by simpa using hv)
  | succ k ih =>
    have hv' : value < 2 ^ (2 ^ k * (2 * size)) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hv
    simp only [popcountTree]
    rw [ih (2 * size) hv']
    have hcount : ∀ i < 2 * size, bitCount (2 ^ k) (value >>> (2 ^ k * i)) < 2 ^ (2 ^ k) :=
      fun i _ => lt_of_le_of_lt (bitCount_le _ _) Nat.lt_two_pow_self
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ]; omega,
      packed_pair_sum (2 ^ k) size _ (Nat.two_pow_pos k) hcount]
    refine packF_congr _ _ _ _ fun i _ => ?_
    rw [show 2 * 2 ^ k = 2 ^ k + 2 ^ k by omega, bitCount_add,
      show 2 ^ k * (2 * i) = (2 ^ k + 2 ^ k) * i by ring,
      show 2 ^ k * (2 * i + 1) = (2 ^ k + 2 ^ k) * i + 2 ^ k by ring]
    simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_add]

/-- On a packed table whose entries are below `2 ^ bits`, with `bits` at most
the lane width `2 ^ k`, the tree returns the bit count of every entry. -/
theorem popcountTree_packF (k size bits : Nat) (f : Nat → Nat) (hbits : bits ≤ 2 ^ k)
    (hf : ∀ i < size, f i < 2 ^ bits) :
    popcountTree k size (packF (2 ^ k) size f) =
      packF (2 ^ k) size (fun i => bitCount bits (f i)) := by
  have hfit : ∀ i < size, f i < 2 ^ 2 ^ k :=
    fun i hi => (hf i hi).trans_le (Nat.pow_le_pow_right Nat.two_pos hbits)
  rw [popcountTree_eq k size _ (packF_lt _ _ _ (Nat.two_pow_pos k) hfit)]
  refine packF_congr _ _ _ _ fun i hi => ?_
  rw [← bitCount_mod, Nat.shiftRight_eq_div_pow, ← lane_eq_div_mod, lane_packF _ _ _ _ hfit,
    if_pos hi, show 2 ^ k = bits + (2 ^ k - bits) by omega, bitCount_extend _ _ _ (hf i hi)]

/-- A constant-digit table can be grouped into equal-sized blocks. -/
lemma packF_constant_group (width cells size value : Nat) :
    packF width (cells * size) (fun _ => value) =
      packF (width * cells) size (fun _ => packF width cells (fun _ => value)) := by
  induction size with
  | zero => simp [packF]
  | succ size ih =>
    rw [Nat.mul_succ, packF_split, ih, packF_succ]
    simp only [Nat.mul_assoc]

/-! ## Lanes of 128 bits -/

/-- The seven masks used by the 128-bit parallel popcount. -/
def popcountMask (k : Fin 7) : Nat :=
  packF (2 ^ (k.val + 1)) (2 ^ (6 - k.val)) (fun _ => 2 ^ (2 ^ k.val) - 1)

/-- One executable parallel pair-summing stage; `r` is the packed table with
`1` in every 128-bit lane. -/
def popcountStep (r value k : Nat) : Nat :=
  let mask := r * popcountMask ⟨k % 7, Nat.mod_lt _ (by decide)⟩
  (value &&& mask) + ((value >>> (2 ^ k)) &&& mask)

/-- Compute 128-bit lane popcounts with seven parallel pair-summing stages. -/
def popcount128 (r value : Nat) : Nat :=
  popcountStep r (popcountStep r (popcountStep r (popcountStep r
    (popcountStep r (popcountStep r (popcountStep r value 0) 1) 2) 3) 4) 5) 6

/-- The seven finite mask constants fit one 128-bit word. -/
lemma popcountMask_lt : ∀ k : Fin 7, popcountMask k < 2 ^ 128 := by decide +kernel

/-- Each 128-bit mask repeats its smaller pair-summing pattern across the
entire batch. -/
lemma popcountMask_repeated (size : Nat) (k : Fin 7) :
    packF 128 size (fun _ => 1) * popcountMask k =
      packF (2 ^ (k.val + 1)) (2 ^ (6 - k.val) * size) (fun _ => 2 ^ (2 ^ k.val) - 1) := by
  rw [repeat_mul_eq_packF, packF_constant_group]
  have he : 2 ^ (k.val + 1) * 2 ^ (6 - k.val) = 128 := by
    fin_cases k <;> decide
  rw [he]
  rfl

/-- The executable seven-stage operation is the generic pair-summing tree. -/
lemma popcount128_eq_tree (size value : Nat) :
    popcount128 (packF 128 size (fun _ => 1)) value = popcountTree 7 size value := by
  unfold popcount128 popcountStep
  simp only [popcountMask_repeated]
  simp only [popcountTree, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub,
    ← Nat.mul_assoc, Nat.reduceMul, Nat.one_mul]

/-- The executable parallel popcount returns the weight of every entry below
`2 ^ 90` in its own 128-bit lane. -/
theorem popcount128_packF (size : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2 ^ 90) :
    popcount128 (packF 128 size (fun _ => 1)) (packF 128 size f) =
      packF 128 size (fun i => bitCount 90 (f i)) := by
  rw [popcount128_eq_tree]
  exact popcountTree_packF 7 size 90 f (by norm_num) hf

end PackedDigits

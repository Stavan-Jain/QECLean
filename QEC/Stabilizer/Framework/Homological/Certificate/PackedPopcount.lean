import QEC.Stabilizer.Framework.Homological.Certificate.PackedLaneShifts
import Mathlib.Tactic.FinCases
set_option maxRecDepth 10000
namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Appending one table entry appends its digit to the packed natural. -/
theorem packF_succ (width size : Nat) (f : Nat → Nat) :
    packF width (size+1) f = packF width size f + 2^(width*size)*f size := by
  rw [packF_split width size 1]
  simp [packF]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Pair adjacent digits into double-width lanes. -/
theorem packF_pair (width size : Nat) (f : Nat → Nat) :
    packF width (2*size) f =
      packF (2*width) size (fun i => f (2*i) + 2^width*f (2*i+1)) := by
  induction size with
  | zero => simp [packF]
  | succ size ih =>
    rw [show 2*(size+1)=2*size+1+1 by omega, packF_succ, packF_succ, ih, packF_succ]
    simp only [Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_assoc]
    ring

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Merging adjacent lanes sums their entries without carry into the next pair. -/
theorem packed_pair_sum (width size : Nat) (f : Nat → Nat) (hw : 0 < width)
    (hf : ∀ i < 2*size, f i < 2^width) :
    let v := packF width (2*size) f
    let mask := packF (2*width) size (fun _ => 2^width-1)
    (v &&& mask) + ((v >>> width) &&& mask) =
      packF (2*width) size (fun i => f (2*i)+f (2*i+1)) := by
  dsimp only
  rw [packF_pair]
  let p := fun i => f (2*i) + 2^width*f (2*i+1)
  have hp : ∀ i < size, p i < 2^(2*width) := by
    intro i hi
    have ha := hf (2*i) (by omega)
    have hb := hf (2*i+1) (by omega)
    dsimp [p]
    rw [show 2*width=width+width by omega, pow_add]
    nlinarith [Nat.two_pow_pos width]
  have hm : 2^width-1 < 2^(2*width) := by
    have hp := Nat.two_pow_pos width
    have hle : 2^width ≤ 2^(2*width) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  change (packF (2*width) size p &&& _) + ((packF (2*width) size p >>> width) &&& _) = _
  rw [packF_and (2*width) size p _ (by omega) hp (fun _ _ => hm),
    masked_shiftRight_packF (2*width) size width (2^width-1) p (by omega) hp hm]
  · rw [packF_add]
    apply packF_congr
    intro i hi
    have ha := hf (2*i) (by omega)
    have hb := hf (2*i+1) (by omega)
    simp [p, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.add_mul_div_left, Nat.div_eq_of_lt ha, Nat.two_pow_pos]
  · intro j hj hge
    rw [Nat.testBit_two_pow_sub_one]
    simp [show ¬ j < width by omega]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Counting set bits never exceeds the inspected bit length. -/
theorem bitCount_le (n value : Nat) : bitCount n value ≤ n := by
  rw [bitCount_eq_card]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One-bit lanes are the bit counts of the corresponding input bits. -/
theorem packF_bitCount_one (size value : Nat) (hv : value < 2^size) :
    value = packF 1 size (fun i => bitCount 1 (value >>> i)) := by
  apply eq_of_lane_eq (by decide : 0 < 1)
  intro i
  rw [lane_packF 1 size i _ (fun j hj => by have := bitCount_le 1 (value >>> j); omega)]
  rw [lane_eq_div_mod]
  simp only [Nat.one_mul, pow_one]
  by_cases hi : i < size
  · simp [hi, bitCount, Nat.shiftRight_eq_div_pow]
  · have hzero : value / 2^i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi,hzero]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Pair-summing stages compute all block popcounts in parallel. -/
def popcountTree : Nat → Nat → Nat → Nat
  | 0, _, value => value
  | k+1, size, value =>
    let prior := popcountTree k (2*size) value
    let mask := packF (2^(k+1)) size (fun _ => 2^(2^k)-1)
    (prior &&& mask) + ((prior >>> (2^k)) &&& mask)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The parallel tree produces the exact popcount in each power-of-two lane. -/
theorem popcountTree_eq (k size value : Nat) (hv : value < 2^(2^k*size)) :
    popcountTree k size value =
      packF (2^k) size (fun i => bitCount (2^k) (value >>> (2^k*i))) := by
  induction k generalizing size with
  | zero => simpa [popcountTree] using packF_bitCount_one size value (by simpa using hv)
  | succ k ih =>
    have hv' : value < 2^(2^k*(2*size)) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hv
    simp only [popcountTree]
    rw [ih (2*size) hv']
    have hw := Nat.two_pow_pos k
    have hcount : ∀ i < 2*size, bitCount (2^k) (value >>> (2^k*i)) < 2^(2^k) :=
      fun i _ => lt_of_le_of_lt (bitCount_le _ _) Nat.lt_two_pow_self
    rw [show 2^(k+1)=2*(2^k) by rw [pow_succ]; omega,
      packed_pair_sum (2^k) size _ hw hcount]
    apply packF_congr
    intro i hi
    rw [show 2*(2^k)=2^k+2^k by omega, bitCount_add]
    have hbase : 2^k*(2*i)=(2^k+2^k)*i := by ring
    have hnext : 2^k*(2*i+1)=(2^k+2^k)*i+2^k := by ring
    rw [hbase,hnext]
    simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_add]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A constant-digit table can be grouped into equal-sized blocks. -/
theorem packF_constant_group (width cells size value : Nat) :
    packF width (cells*size) (fun _ => value) =
      packF (width*cells) size (fun _ => packF width cells (fun _ => value)) := by
  induction size with
  | zero => simp [packF]
  | succ size ih =>
    rw [Nat.mul_succ, packF_split, ih, packF_succ]
    simp only [Nat.mul_assoc]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The seven masks used by the128-bit parallel popcount. -/
def popcountMask (k : Fin 7) : Nat :=
  packF (2^(k.val+1)) (2^(6-k.val)) (fun _ => 2^(2^k.val)-1)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- One executable parallel pair-summing stage. -/
def popcountStep (r value k : Nat) : Nat :=
  let mask := r * popcountMask ⟨k%7,Nat.mod_lt _ (by decide)⟩
  (value &&& mask) + ((value >>> (2^k)) &&& mask)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Compute128-bit lane popcounts with seven parallel pair-summing stages. -/
def popcount128 (r value : Nat) : Nat :=
  popcountStep r (popcountStep r (popcountStep r (popcountStep r
    (popcountStep r (popcountStep r (popcountStep r value 0) 1) 2) 3) 4) 5) 6

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The seven finite mask constants fit one128-bit word. -/
theorem popcountMask_lt : ∀ k : Fin 7, popcountMask k < 2^128 := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each128-bit mask repeats its smaller pair-summing pattern across the entire batch. -/
theorem popcountMask_repeated (size : Nat) (k : Fin 7) :
    packF 128 size (fun _ => 1) * popcountMask k =
      packF (2^(k.val+1)) (2^(6-k.val)*size) (fun _ => 2^(2^k.val)-1) := by
  rw [repeat_mul_eq_packF, packF_constant_group]
  have he : 2^(k.val+1)*2^(6-k.val) = 128 := by
    fin_cases k <;> decide
  rw [he]
  rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The executable seven-stage operation is the generic proved pair-summing tree. -/
theorem popcount128_eq_tree (size value : Nat) :
    popcount128 (packF 128 size (fun _ => 1)) value = popcountTree 7 size value := by
  unfold popcount128 popcountStep
  simp only [popcountMask_repeated]
  simp only [popcountTree, Fin.val_mk, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub,
    ← Nat.mul_assoc, Nat.reduceMul, Nat.one_mul]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A zero word has no set bits. -/
theorem bitCount_zero_word (bits : Nat) : bitCount bits 0 = 0 := by
  rw [bitCount_eq_card]
  simp

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Extending the inspection range does not change a bounded word's popcount. -/
theorem bitCount_extend (bits extra value : Nat) (hv : value < 2^bits) :
    bitCount (bits+extra) value = bitCount bits value := by
  rw [bitCount_add, Nat.div_eq_of_lt hv, bitCount_zero_word, Nat.add_zero]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The executable parallel popcount returns the90-bit chain weight in every128-bit lane. -/
theorem popcount128_packF (size : Nat) (f : Nat → Nat)
    (hf : ∀ i < size, f i < 2^90) :
    popcount128 (packF 128 size (fun _ => 1)) (packF 128 size f) =
      packF 128 size (fun i => bitCount 90 (f i)) := by
  have hfit : ∀ i < size, f i < 2^128 :=
    fun i hi => lt_trans (hf i hi) (by norm_num)
  rw [popcount128_eq_tree, popcountTree_eq 7 size _
    (by simpa using packF_lt 128 size f (by decide) hfit)]
  change packF 128 size (fun i => bitCount 128 (packF 128 size f >>> (128*i))) = _
  apply packF_congr
  intro i hi
  rw [← bitCount_mod]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [← lane_eq_div_mod]
  rw [lane_packF 128 size i f hfit, if_pos hi]
  exact bitCount_extend 90 38 (f i) (hf i hi)

end PackedDigits

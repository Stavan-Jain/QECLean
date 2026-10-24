import QEC.Stabilizer.Framework.Homological.Certificate.SmallMaskPair
import QEC.Stabilizer.Framework.Homological.Certificate.ParityFold
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear
import Mathlib.Data.List.Basic

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A finite list of positions specifies a bitset by setting exactly those bits. -/
def listedBits : List Nat → Nat
  | [] => 0
  | q :: qs => 2^q ||| listedBits qs

/-- A bit of a listed bitset is set precisely when its position occurs in the list. -/
theorem listedBits_testBit (qs : List Nat) (i : Nat) :
    (listedBits qs).testBit i = decide (i ∈ qs) := by
  induction qs with
  | nil => simp [listedBits]
  | cons q qs ih =>
    simp [listedBits, Nat.testBit_or, Nat.testBit_two_pow, ih, eq_comm]

/-- A surviving encoded pair belongs to the explicitly listed outside masks. -/
theorem pair_mem_of_listed_bit (n width q r expected : Nat) (codes : List Nat)
    (hw : 0 < width) (hr : r < width)
    (he : expected = listedBits codes) (hbit : expected.testBit (width*q+r) = true) :
    pairMask n q r ∈ codes.map (fun c => pairMask n (c/width) (c%width)) := by
  rw [he, listedBits_testBit] at hbit
  have hm : width*q+r ∈ codes := of_decide_eq_true hbit
  apply List.mem_map.mpr
  refine ⟨width*q+r,hm,?_⟩
  simp [Nat.add_comm, Nat.add_mul_div_left, Nat.div_eq_of_lt hr,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, hw]

/-- XOR of two folded parity bits is the parity of the XOR. -/
theorem parityFold_xor (k a b : Nat) :
    parityFold k (a ^^^ b) = parityFold k a ^^^ parityFold k b := by
  have ha : bitCount (2^k) a % 2 < 2^1 := Nat.mod_lt _ (by decide)
  have hb : bitCount (2^k) b % 2 < 2^1 := Nat.mod_lt _ (by decide)
  have hx := Nat.xor_lt_two_pow ha hb
  rw [parityFold_eq, parityFold_eq, parityFold_eq, bitCount_xor_mod_two]
  rw [← Nat.mod_eq_of_lt hx, Nat.xor_mod_two_eq]
  simp [Nat.add_mod]

/-- One bounded coordinate has exactly one set bit in any containing prefix. -/
theorem bitCount_two_pow (bits q : Nat) (hq : q < bits) : bitCount bits (2^q) = 1 := by
  rw [bitCount_eq_card]
  have hs : (Finset.range bits).filter (fun i => (2^q).testBit i = true) = {q} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_two_pow,
      decide_eq_true_eq, Finset.mem_singleton]
    omega
  rw [hs, Finset.card_singleton]

/-- A plane's value on a sentinel singleton is its coordinate bit. -/
theorem parityFold_singletonMask (n k p q : Nat) (hn : n ≤ 2^k)
    (hp : p < 2^n) (hq : q ≤ n) :
    parityFold k (p &&& singletonMask n q) = if p.testBit q then 1 else 0 := by
  by_cases hq' : q < n
  · rw [singletonMask, if_pos hq', Nat.and_two_pow]
    cases hbit : p.testBit q
    · simp [parityFold_eq, bitCount_eq_card]
    · simp only [Bool.toNat_true, Nat.one_mul, ite_true]
      rw [parityFold_eq, bitCount_two_pow _ _ (by omega)]
  · have he : q = n := by omega
    subst q
    rw [singletonMask, if_neg (lt_irrefl n), Nat.and_zero,
      Nat.testBit_eq_false_of_lt hp]
    simp [parityFold_eq, bitCount_eq_card]

/-- A plane evaluates an encoded pair by XORing the two coordinate bits. -/
theorem parityFold_pairMask (n k p q r : Nat) (hn : n ≤ 2^k)
    (hp : p < 2^n) (hq : q ≤ n) (hr : r ≤ n) :
    parityFold k (p &&& pairMask n q r) =
      if p.testBit q ^^ p.testBit r then 1 else 0 := by
  rw [pairMask, Nat.and_xor_distrib_left, parityFold_xor,
    parityFold_singletonMask n k p q hn hp hq,
    parityFold_singletonMask n k p r hn hp hr]
  cases p.testBit q <;> cases p.testBit r <;> decide

/-- A singleton at a zero shadow bit is disjoint from that shadow. -/
theorem singletonMask_and_zero (n beta q : Nat) (hq : beta.testBit q = false) :
    singletonMask n q &&& beta = 0 := by
  by_cases hn : q < n
  · rw [singletonMask,if_pos hn,Nat.and_comm,Nat.and_two_pow,hq]
    simp
  · simp [singletonMask,hn]

/-- Two zero shadow bits represent a support disjoint from the shadow. -/
theorem pairMask_and_zero (n beta q r : Nat)
    (hq : beta.testBit q = false) (hr : beta.testBit r = false) :
    pairMask n q r &&& beta = 0 := by
  rw [pairMask,Nat.and_xor_distrib_right,singletonMask_and_zero n beta q hq,
    singletonMask_and_zero n beta r hr,Nat.xor_self]

end Quantum.Stabilizer.Homological.F2Mask

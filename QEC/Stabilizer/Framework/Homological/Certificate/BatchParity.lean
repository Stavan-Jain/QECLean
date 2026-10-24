import QEC.Stabilizer.Framework.Homological.Certificate.OrbitPackedExtra
import QEC.Stabilizer.Framework.Homological.Certificate.ParityFold

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- The unmasked logarithmic parity fold operates on every starting bit simultaneously. -/
def rawParityFold : Nat → Nat → Nat
  | 0, x => x
  | k+1, x => rawParityFold k (Nat.xor x (Nat.shiftRight x (2^k)))

/-- Uniform right shifts commute with the unmasked parity fold. -/
theorem rawParityFold_shift (k x j : Nat) :
    rawParityFold k x >>> j = rawParityFold k (x >>> j) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [rawParityFold, ih]
    congr 1
    change (x ^^^ (x >>> 2 ^ k)) >>> j = (x >>> j) ^^^ ((x >>> j) >>> 2 ^ k)
    rw [Nat.shiftRight_xor_distrib]
    simp only [← Nat.shiftRight_add, Nat.add_comm]

/-- Reading the low bit of the unmasked fold gives the certified parity. -/
theorem rawParityFold_mod_two (k x : Nat) :
    rawParityFold k x % 2 = parityFold k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simpa only [rawParityFold, parityFold] using ih (Nat.xor x (Nat.shiftRight x (2^k)))

/-- A bit of the unmasked fold is the parity of the block beginning at that bit. -/
theorem rawParityFold_testBit (k x j : Nat) :
    (rawParityFold k x).testBit j = decide (bitCount (2^k) (x >>> j) % 2 = 1) := by
  have h := congrArg (fun v : Nat => v % 2) (rawParityFold_shift k x j)
  dsimp only at h
  rw [rawParityFold_mod_two, parityFold_eq] at h
  simpa only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow] using
    congrArg (fun v => decide (v = 1)) h

/-- Restricting a larger lane does not change the number of bits in a shorter prefix. -/
theorem bitCount_lane_prefix (width index bits x : Nat) (hb : bits ≤ width) :
    bitCount bits (lane width index x) = bitCount bits (x >>> (width*index)) := by
  rw [lane_eq_div_mod]
  rw [← bitCount_mod bits (x / 2^(width*index) % 2^width), Nat.mod_mod_of_dvd]
  · rw [bitCount_mod, Nat.shiftRight_eq_div_pow]
  · exact Nat.pow_dvd_pow 2 hb

/-- Reading the low bit of each packed lane gives its independent parity. -/
theorem rawParityFold_lane (width size k index : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hk : 2^k ≤ width)
    (hf : ∀ i < size, f i < 2^width) (hi : index < size) :
    (rawParityFold k (packF width size f)).testBit (width*index) =
      decide (bitCount (2^k) (f index) % 2 = 1) := by
  rw [rawParityFold_testBit]
  have h := bitCount_lane_prefix width index (2^k) (packF width size f) hk
  rw [lane_packF _ _ _ _ hf, if_pos hi] at h
  rw [← h]

/-- A successful packed parity-one check certifies every lane. -/
theorem rawParityFold_all_odd (width size k : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hk : 2^k ≤ width)
    (hf : ∀ i < size, f i < 2^width)
    (hcheck : rawParityFold k (packF width size f) &&& packF width size (fun _ => 1) =
      packF width size (fun _ => 1)) :
    ∀ i < size, bitCount (2^k) (f i) % 2 = 1 := by
  intro i hi
  have hone : ∀ j < size, (1 : Nat) < 2^width := fun _ _ => Nat.one_lt_two_pow hw.ne'
  have hm : (packF width size (fun _ => 1)).testBit (width*i) = true := by
    simpa [hi] using testBit_packF_at width size i 0 (fun _ => 1) hone hw
  have h := congrArg (fun x => x.testBit (width*i)) hcheck
  dsimp only at h
  rw [Nat.testBit_and, hm, Bool.and_true,
    rawParityFold_lane _ _ _ _ _ hw hk hf hi] at h
  exact of_decide_eq_true h

#print axioms rawParityFold_all_odd
end PackedDigits

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Parallel parity produces exactly one certified binary parity digit per lane. -/
theorem rawParityFold_packF (width size k : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hk : 2^k ≤ width)
    (hf : ∀ i < size, f i < 2^width) :
    rawParityFold k (packF width size f) &&& packF width size (fun _ => 1) =
      packF width size (fun i => parityFold k (f i)) := by
  have hone : (1 : Nat) < 2^width := Nat.one_lt_two_pow hw.ne'
  have hp : ∀ i < size, parityFold k (f i) < 2^width := by
    intro i hi
    rw [parityFold_eq]
    have hm := Nat.mod_lt (bitCount (2^k) (f i)) (by decide : 0 < 2)
    omega
  apply eq_of_lane_eq hw
  intro i
  rw [lane_and,lane_packF _ _ _ _ (fun _ _ => hone),lane_packF _ _ _ _ hp]
  by_cases hi : i < size
  · simp only [if_pos hi]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    by_cases hj : j = 0
    · subst j
      rw [Nat.testBit_one_zero,Bool.and_true,testBit_lane]
      simp only [Nat.add_zero,show decide (0 < width) = true from decide_eq_true hw,Bool.true_and]
      rw [rawParityFold_lane _ _ _ _ _ hw hk hf hi,parityFold_eq]
      simp only [Nat.testBit_zero,Nat.mod_mod,Bool.and_true]
    · have h1 : (1 : Nat).testBit j = false := by
        simpa using Nat.testBit_two_pow_of_ne (Ne.symm hj)
      rw [h1,Bool.and_false]
      have hpar : parityFold k (f i) < 2^j := by
        rw [parityFold_eq]
        exact lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 2))
          (Nat.pow_le_pow_right (show 1 ≤ (2 : Nat) by decide) (by omega : 1 ≤ j))
      exact (Nat.testBit_lt_two_pow hpar).symm
  · simp [hi]

#print axioms rawParityFold_packF
end PackedDigits

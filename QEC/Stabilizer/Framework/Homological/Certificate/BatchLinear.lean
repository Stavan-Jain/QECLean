import QEC.Stabilizer.Framework.Homological.Certificate.OrbitPackedExtra
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- One selected bit in every packed word becomes a lane of zero or one. -/
theorem packF_selectBit (width size bit : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hb : bit < width)
    (hf : ∀ i < size, f i < 2 ^ width) :
    (packF width size f >>> bit) &&& packF width size (fun _ => 1) =
      packF width size (fun i => if (f i).testBit bit then 1 else 0) := by
  have hone : ∀ i < size, (1 : Nat) < 2 ^ width := fun _ _ => Nat.one_lt_two_pow hw.ne'
  have hsel : ∀ i < size, (if (f i).testBit bit then 1 else 0) < 2 ^ width := by
    intro i hi
    have h := hone i hi
    split <;> omega
  apply eq_of_lane_eq hw
  intro i
  rw [lane_and, lane_packF _ _ _ _ hone, lane_packF _ _ _ _ hsel]
  by_cases hi : i < size
  · simp only [if_pos hi]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, testBit_lane, Nat.testBit_shiftRight]
    by_cases hj : j = 0
    · subst j
      simp only [Nat.add_zero, Nat.testBit_one_zero, Bool.and_true,
        show decide (0 < width) = true from decide_eq_true hw]
      rw [Nat.add_comm bit (width * i), testBit_packF_at _ _ _ _ _ hf hb, if_pos hi]
      cases (f i).testBit bit <;> decide
    · have h1 : (1 : Nat).testBit j = false := by
        rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow_of_ne (Ne.symm hj)]
      simp [h1]
      split <;> simp [h1]
  · simp [hi]

/-- Perform a binary reconstruction simultaneously in all packed lanes. -/
def batchRecon (rep coeff : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (bit,row) :: rest =>
      ((coeff >>> bit) &&& rep) * row ^^^ batchRecon rep coeff rest

/-- Packed reconstruction is exactly the existing binary reconstruction in each lane. -/
theorem batchRecon_packF (width size : Nat) (f : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2 ^ width)
    (w : List (Nat × Nat)) (hrows : ∀ p ∈ w, p.1 < width ∧ p.2 < 2 ^ width) :
    batchRecon (packF width size (fun _ => 1)) (packF width size f) w =
      packF width size (fun i => reconX w (f i)) := by
  induction w with
  | nil => simp [batchRecon, reconX, packF]
  | cons p ps ih =>
    have hp := hrows p (by simp)
    have hps : ∀ q ∈ ps, q.1 < width ∧ q.2 < 2 ^ width := fun q hq => hrows q (by simp [hq])
    rw [batchRecon, packF_selectBit _ _ _ _ hw hp.1 hf, Nat.mul_comm,
      packF_mul, ih hps]
    have hs : ∀ i < size, p.2 * (if (f i).testBit p.1 then 1 else 0) < 2 ^ width := by
      intro i hi
      split <;> simp_all
    rw [packF_xor _ _ _ _ hw hs (fun i _ => reconX_lt ps (f i) width (fun q hq => (hps q hq).2))]
    apply packF_congr
    intro i hi
    simp only [reconX, List.filter_cons]
    cases (f i).testBit p.1 <;> simp [xorList_cons]

#print axioms batchRecon_packF
end PackedDigits

namespace PackedDigits
/-- A right shift followed by a sufficiently short mask cannot mix adjacent lanes. -/
theorem packF_shiftRight_and (width size bits shift : Nat) (f g : Nat → Nat)
    (hw : 0 < width) (hfit : bits + shift ≤ width)
    (hf : ∀ i < size, f i < 2^width) (hg : ∀ i < size, g i < 2^bits) :
    (packF width size f >>> shift) &&& packF width size g =
      packF width size (fun i => (f i >>> shift) &&& g i) := by
  have hgw : ∀ i < size, g i < 2^width := fun i hi =>
    lt_of_lt_of_le (hg i hi) (Nat.pow_le_pow_right (by decide) (by omega))
  have hr : ∀ i < size, ((f i >>> shift) &&& g i) < 2^width :=
    fun i hi => lt_of_le_of_lt Nat.and_le_right (hgw i hi)
  apply eq_of_lane_eq hw
  intro i
  rw [lane_and, lane_packF _ _ _ _ hgw, lane_packF _ _ _ _ hr]
  by_cases hi : i < size
  · simp only [if_pos hi]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hj : j < bits
    · rw [testBit_lane, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
      have hbw : j < width := by omega
      have hsw : shift+j < width := by omega
      rw [show shift + (width*i+j) = width*i+(shift+j) by omega,
        testBit_packF_at _ _ _ _ _ hf hsw, if_pos hi]
      simp [hbw]
    · have hz : (g i).testBit j = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (hg i hi) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hz]
  · simp [hi]
end PackedDigits

namespace PackedDigits
/-- A bounded packed integer is recovered from all of its lanes. -/
theorem packF_lanes (width size value : Nat) (hw : 0 < width)
    (hv : value < 2^(width*size)) :
    packF width size (fun i => lane width i value) = value := by
  apply eq_of_lane_eq hw
  intro i
  rw [lane_packF _ _ _ _ (fun _ _ => lane_lt _ _ _)]
  by_cases hi : i < size
  · simp [hi]
  · have hlt : value < 2^(width*i) := lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left width (by omega)))
    simp [hi, lane_eq_div_mod, Nat.div_eq_of_lt hlt]
end PackedDigits

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A certified packed reconstruction places each output lane in the generator span. -/
theorem batchRecon_mem_span (width size coeff output : Nat) (hw : 0 < width)
    (hcoeff : coeff < 2^(width*size)) (rows : List (Nat × Nat))
    (hrows : ∀ p ∈ rows, p.1 < width ∧ p.2 < 2^width)
    (hcheck : batchRecon (packF width size (fun _ => 1)) coeff rows = output) :
    ∀ i < size, XorSpan (rows.map Prod.snd) (lane width i output) := by
  rw [← packF_lanes width size coeff hw hcoeff,
    batchRecon_packF width size (fun i => lane width i coeff) hw
      (fun _ _ => lane_lt _ _ _) rows hrows] at hcheck
  intro i hi
  rw [← hcheck, lane_packF _ _ _ _
    (fun j _ => reconX_lt rows (lane width j coeff) width (fun p hp => (hrows p hp).2)), if_pos hi]
  exact reconX_mem_span rows (lane width i coeff)

#print axioms batchRecon_mem_span
end PackedDigits

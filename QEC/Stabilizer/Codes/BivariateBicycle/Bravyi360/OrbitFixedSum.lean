import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.GBOrbitAction
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

namespace Quantum.Stabilizer.Homological.GBOrbit
open PackedDigits

/-- A fixed-mask sentinel detects equality with one translated word. -/
theorem fixedMask_word_bit (w i : Nat) (hw : w < 2^90) (hi : i < 45) :
    (fixedMask w).testBit (128*i+90) =
      decide (entry (w%2^45) (w/2^45) i = w) := by
  have h := packed_equal_mask_bit 128 45 90 w i
    (entry (w%2^45) (w/2^45)) (by decide) (fun j _ => entry_lt _ _ j) hw hi
  unfold fixedMask
  rw [sentinelPattern_eq, repeatPattern_eq, payloadPattern_eq]
  change (packF 128 45 (fun _ => 2^90) ^^^
    (((packOrbit (w%2^45) (w/2^45) ^^^ w*packF 128 45 (fun _ => 1)) +
      packF 128 45 (fun _ => 2^90-1)) &&& packF 128 45 (fun _ => 2^90))).testBit
        (128*i+90) = _
  rw [packOrbit_eq (lowBlock_lt _) (highBlock_lt hw), packF_mul]
  simp only [Nat.mul_one]
  simpa only [testBit_lane, show 90 < 128 from by decide, decide_true, Bool.and_true] using h

/-- The fixed-point count is the sum of45 scalar equality flags. -/
theorem fixedCount_eq_sum (w : Nat) (hw : w < 2^90) :
    fixedCount (fixedMask w) =
      ((List.range 45).map fun i => if entry (w%2^45) (w/2^45) i = w then 1 else 0).sum := by
  rw [← List.sum_toFinset _ (List.nodup_range (n := 45))]
  simp only [List.toFinset_range, Finset.sum_boole]
  unfold fixedCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [fixedMask_word_bit w i hw (Finset.mem_range.mp hi)]
  simp

end Quantum.Stabilizer.Homological.GBOrbit

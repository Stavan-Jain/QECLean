import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear
import QEC.Stabilizer.Framework.Homological.Certificate.BatchParity

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A zero packed intersection certifies a zero intersection in every lane. -/
theorem packF_and_eq_zero (width size : Nat) (f g : Nat → Nat)
    (hw : 0 < width) (hf : ∀ i < size, f i < 2^width)
    (hg : ∀ i < size, g i < 2^width)
    (h : packF width size f &&& packF width size g = 0) :
    ∀ i < size, f i &&& g i = 0 := by
  intro i hi
  have h' := congrArg (lane width i) h
  rw [lane_and, lane_packF _ _ _ _ hf, lane_packF _ _ _ _ hg,
    if_pos hi, if_pos hi] at h'
  simpa [lane] using h'

/-- A packed matrix/dual check certifies annihilation and odd right-hand side in every lane. -/
theorem batchDual0_sound (width size bits k : Nat) (beta coeff : Nat → Nat)
    (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : ∀ i < size, beta i < 2^bits)
    (hc : ∀ i < size, coeff i < 2^width)
    (rows : List (Nat × Nat))
    (hrows : ∀ p ∈ rows, p.1 < width ∧ p.2 < 2^width)
    (hz : batchRecon (packF width size (fun _ => 1)) (packF width size coeff) rows &&&
      packF width size beta = 0)
    (ho : rawParityFold k
      ((batchRecon (packF width size (fun _ => 1)) (packF width size coeff) rows >>> bits) &&&
        packF width size beta) &&& packF width size (fun _ => 1) =
      packF width size (fun _ => 1)) :
    ∀ i < size, reconX rows (coeff i) &&& beta i = 0 ∧
      bitCount (2^k) ((reconX rows (coeff i) >>> bits) &&& beta i) % 2 = 1 := by
  have hbwidth : ∀ i < size, beta i < 2^width := fun i hi =>
    lt_of_lt_of_le (hb i hi) (Nat.pow_le_pow_right (by decide) (by omega))
  have he : ∀ i < size, reconX rows (coeff i) < 2^width :=
    fun i _ => reconX_lt rows (coeff i) width (fun p hp => (hrows p hp).2)
  rw [batchRecon_packF _ _ _ hw hc rows hrows] at hz ho
  rw [packF_shiftRight_and _ _ _ _ _ _ hw hfit he hb] at ho
  have hp := rawParityFold_all_odd width size k
    (fun i => (reconX rows (coeff i) >>> bits) &&& beta i) hw hk
    (fun i hi => lt_of_le_of_lt Nat.and_le_right (hbwidth i hi)) ho
  intro i hi
  exact ⟨packF_and_eq_zero _ _ _ _ hw he hbwidth hz i hi, hp i hi⟩

#print axioms batchDual0_sound
end PackedDigits

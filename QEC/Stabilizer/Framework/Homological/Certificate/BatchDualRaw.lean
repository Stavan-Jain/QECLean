import QEC.Stabilizer.Framework.Homological.Certificate.BatchDualSemantics

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A parallel short mask proves the bit bound of every packed lane. -/
theorem lane_bound_of_parallel_mask (width size bits value : Nat)
    (hw : 0 < width) (hbits : bits ≤ width)
    (hmask : value &&& ((packF width size (fun _ => 1)) * (2^bits-1)) = value) :
    ∀ i < size, lane width i value < 2^bits := by
  have hm : (2^bits-1 : Nat) < 2^width := lt_of_lt_of_le
    (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
    (Nat.pow_le_pow_right (by decide) hbits)
  rw [Nat.mul_comm,packF_mul] at hmask
  simp only [Nat.mul_one] at hmask
  intro i hi
  have h := congrArg (lane width i) hmask
  rw [lane_and,lane_packF _ _ _ _ (fun _ _ => hm),if_pos hi] at h
  calc
    lane width i value = lane width i value &&& (2^bits-1) := h.symm
    _ ≤ 2^bits-1 := Nat.and_le_right
    _ < 2^bits := Nat.sub_lt (Nat.two_pow_pos _) (by decide)

/-- The raw packed dual checker certifies each lane without iterating over its records. -/
theorem batchDual0_raw_sound (width size bits k beta coeff : Nat)
    (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : beta < 2^(width*size)) (hc : coeff < 2^(width*size))
    (hmask : beta &&& ((packF width size (fun _ => 1)) * (2^bits-1)) = beta)
    (rows : List (Nat × Nat))
    (hrows : ∀ p ∈ rows, p.1 < width ∧ p.2 < 2^width)
    (hz : batchRecon (packF width size (fun _ => 1)) coeff rows &&& beta = 0)
    (ho : rawParityFold k ((batchRecon (packF width size (fun _ => 1)) coeff rows >>> bits) &&& beta) &&&
      packF width size (fun _ => 1) = packF width size (fun _ => 1)) :
    ∀ i < size, reconX rows (lane width i coeff) &&& lane width i beta = 0 ∧
      parityFold k ((reconX rows (lane width i coeff) >>> bits) &&& lane width i beta) = 1 := by
  have hbeta := lane_bound_of_parallel_mask width size bits beta hw (by omega) hmask
  have h := batchDual0_sound width size bits k
    (fun i => lane width i beta) (fun i => lane width i coeff) hw hfit hk hbeta
    (fun _ _ => lane_lt _ _ _) rows hrows
  rw [packF_lanes _ _ _ hw hc,packF_lanes _ _ _ hw hb] at h
  intro i hi
  obtain ⟨hzero,hodd⟩ := h hz ho i hi
  exact ⟨hzero,by simpa [parityFold_eq] using hodd⟩

#print axioms batchDual0_raw_sound
end PackedDigits

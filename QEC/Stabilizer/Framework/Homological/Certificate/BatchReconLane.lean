import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Reading a lane after a packed reconstruction gives the ordinary reconstruction
of that input lane. -/
theorem batchRecon_lane (width size coeff : Nat)
    (hw : 0 < width) (hc : coeff < 2 ^ (width * size))
    (rows : List (Nat × Nat))
    (hr : ∀ p ∈ rows, p.1 < width ∧ p.2 < 2 ^ width)
    (i : Nat) (hi : i < size) :
    lane width i (batchRecon (packF width size (fun _ => 1)) coeff rows) =
      reconX rows (lane width i coeff) := by
  have h := batchRecon_packF width size (fun j => lane width j coeff) hw
    (fun _ _ => lane_lt _ _ _) rows hr
  rw [packF_lanes width size coeff hw hc] at h
  rw [h, lane_packF _ _ _ _
    (fun j _ => reconX_lt rows (lane width j coeff) width (fun p hp => (hr p hp).2)),
    if_pos hi]

/-- Two simultaneous matrix checks certify the specified shadow and support
containment separately in every packed lane. -/
theorem batchFlat_sound (width e coeff beta : Nat) (hw : 0 < width)
    (hc : coeff < 2 ^ (width * 2 ^ e))
    (sheet shadow : List (Nat × Nat))
    (hsheet : ∀ p ∈ sheet, p.1 < width ∧ p.2 < 2 ^ width)
    (hshadow : ∀ p ∈ shadow, p.1 < width ∧ p.2 < 2 ^ width)
    (hpush : batchRecon (repeatBlock 1 width e) coeff shadow = beta)
    (hflat : batchRecon (repeatBlock 1 width e) coeff sheet &&&
      ((2 ^ (width * 2 ^ e) - 1) ^^^ beta) = 0)
    (i : Nat) (hi : i < 2 ^ e) :
    reconX shadow (lane width i coeff) = lane width i beta ∧
      reconX sheet (lane width i coeff) &&&
        ((2 ^ width - 1) ^^^ lane width i beta) = 0 := by
  have hrep := repeatBlock_eq_packF 1 width e hw (Nat.one_lt_two_pow hw.ne')
  have hp := congrArg (lane width i) hpush
  rw [hrep, batchRecon_lane width (2 ^ e) coeff hw hc shadow hshadow i hi] at hp
  refine ⟨hp, ?_⟩
  have hf := congrArg (lane width i) hflat
  rw [lane_and, lane_xor, hrep,
    batchRecon_lane width (2 ^ e) coeff hw hc sheet hsheet i hi,
    ← repeatBlock_lowMask width e hw,
    lane_repeatBlock _ _ _ _ hw (Nat.sub_lt (Nat.two_pow_pos _) (by omega)),
    if_pos hi] at hf
  simpa [lane] using hf

end PackedDigits

import QEC.Stabilizer.Framework.Homological.Certificate.BatchCap1
import QEC.Stabilizer.Framework.Homological.Certificate.Cap1Scalar
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DualConstraints
import QEC.Stabilizer.Framework.Homological.Certificate.OutsideMaskBounds

noncomputable section

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Parallel cap-one filters retain their exact lane values and all annihilator equations. -/
theorem batchCap1_raw_sound (width size bits k beta allowed zero : Nat) (coeffs : List Nat)
    (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width)
    (hb : beta < 2^(width*size))
    (hbeta : beta &&& (packF width size (fun _ => 1) * (2^bits-1)) = beta)
    (hc : ∀ c ∈ coeffs, c < 2^(width*size))
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width)
    (hann : ∀ c ∈ coeffs, batchRecon (packF width size (fun _ => 1)) c rows &&& beta = 0)
    (ha : batchAllowed1 bits k (packF width size (fun _ => 1)) beta rows coeffs = allowed)
    (hz : batchZero1 bits k (packF width size (fun _ => 1)) beta rows coeffs = zero)
    (i : Nat) (hi : i < size) :
    let zs := coeffs.map (fun c => reconX rows (lane width i c))
    scalarAllowed1 bits k (lane width i beta) zs = lane width i allowed ∧
    scalarZero1 bits k (lane width i beta) zs = lane width i zero ∧
    ∀ c ∈ coeffs, reconX rows (lane width i c) &&& lane width i beta = 0 := by
  have hbs := lane_bound_of_parallel_mask width size bits beta hw (by omega) hbeta
  have hfs : ∀ f ∈ coeffs.map (fun c => fun j => lane width j c), ∀ j < size, f j < 2^width := by
    intro f hf j hj
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hf
    exact lane_lt _ _ _
  have hmap : (coeffs.map (fun c => fun j => lane width j c)).map (fun f => packF width size f) = coeffs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id coeffs]
    apply List.map_congr_left
    intro c hmem
    exact packF_lanes width size c hw (hc c hmem)
  have ha' := batchAllowed1_packF width size bits k (fun j => lane width j beta)
    (coeffs.map fun c => fun j => lane width j c) hw hfit hk hbs hfs rows hr
  have hz' := batchZero1_packF width size bits k (fun j => lane width j beta)
    (coeffs.map fun c => fun j => lane width j c) hw hfit hk hbs hfs rows hr
  rw [hmap,packF_lanes _ _ _ hw hb,ha] at ha'
  rw [hmap,packF_lanes _ _ _ hw hb,hz] at hz'
  have haLane := congrArg (lane width i) ha'
  have hzLane := congrArg (lane width i) hz'
  have hpow : 2^bits ≤ 2^width := Nat.pow_le_pow_right (by decide) (by omega)
  rw [lane_packF _ _ _ _ (fun j hj => (scalarAllowed1_lt _ _ _ _ (hbs j hj)).trans_le hpow),if_pos hi] at haLane
  rw [lane_packF _ _ _ _ (fun j hj => (scalarZero1_lt _ _ _ _).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw)),if_pos hi] at hzLane
  refine ⟨?_,?_,?_⟩
  · simpa only [List.map_map,Function.comp_apply] using haLane.symm
  · simpa only [List.map_map,Function.comp_apply] using hzLane.symm
  · intro c hcm
    have he := batchRecon_packF width size (fun j => lane width j c) hw
      (fun j hj => lane_lt _ _ _) rows hr
    rw [packF_lanes _ _ _ hw (hc c hcm)] at he
    have heq := hann c hcm
    rw [he,← packF_lanes width size beta hw hb,
      packF_and _ _ _ _ hw (fun j hj => reconX_lt rows _ width (fun p hp => (hr p hp).2))
        (fun j hj => lane_lt _ _ _)] at heq
    have hl := congrArg (lane width i) heq
    rw [lane_packF _ _ _ _ (fun j hj => lt_of_le_of_lt Nat.and_le_right (lane_lt _ _ _)),if_pos hi] at hl
    simpa [lane] using hl

end PackedDigits

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- Every outside-support mask is disjoint from its shadow. -/
theorem outsideMask_disjoint (word beta : Nat) : outsideMask word beta &&& beta = 0 := by
  simp only [outsideMask,Nat.and_xor_distrib_right,Nat.and_assoc,Nat.and_self,Nat.xor_self]

/-- Empty singleton and zero-support flags exclude every solution with at
most one outside coordinate. -/
theorem cap1_impossible_of_duals (bits k beta word : Nat) (zs : List Nat)
    (hbits : bits ≤ 2^k) (hw : word < 2^bits)
    (hoff : bitCount bits (outsideMask word beta) ≤ 1)
    (he : ∀ z ∈ zs, parityFold k (z &&& outsideMask word beta) =
      parityFold k ((z >>> bits) &&& beta))
    (ha : scalarAllowed1 bits k beta zs = 0) (hz : scalarZero1 bits k beta zs = 0) : False := by
  have hc := scalar_cap1_complete bits k beta (outsideMask word beta) zs hbits
    (outsideMask_lt _ _ _ hw) hoff (outsideMask_disjoint word beta) he
  rcases hc with ⟨_,hc⟩ | ⟨q,hq,_,hc⟩
  · omega
  · simp [ha] at hc

end Quantum.Stabilizer.Homological.F2Mask

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A parallel cap-one certificate with empty filters rules out every corresponding fiber. -/
theorem cap1_raw_impossible (width size bits k beta : Nat) (coeffs : List Nat)
    (hw : 0 < width) (hfit : bits+bits ≤ width) (hk : 2^k ≤ width) (hbits : bits ≤ 2^k)
    (hb : beta < 2^(width*size))
    (hbeta : beta &&& (packF width size (fun _ => 1) * (2^bits-1)) = beta)
    (rows E R : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width)
    (hc : ∀ c ∈ coeffs, c < 2^(width*size))
    (hann : ∀ c ∈ coeffs, batchRecon (packF width size (fun _ => 1)) c rows &&& beta = 0)
    (ha : batchAllowed1 bits k (packF width size (fun _ => 1)) beta rows coeffs = 0)
    (hz : batchZero1 bits k (packF width size (fun _ => 1)) beta rows coeffs = 0)
    (hconstraint : ∀ coeff beta word, word < 2^bits → reconX rows coeff &&& beta = 0 →
      reconX E word = reconX R beta →
      parityFold k (reconX rows coeff &&& outsideMask word beta) =
        parityFold k ((reconX rows coeff >>> bits) &&& beta))
    (i : Nat) (hi : i < size) (word : Nat) (hword : word < 2^bits)
    (he : reconX E word = reconX R (lane width i beta))
    (hoff : bitCount bits (outsideMask word (lane width i beta)) ≤ 1) : False := by
  have hs := batchCap1_raw_sound width size bits k beta 0 0 coeffs hw hfit hk hb hbeta
    hc rows hr hann ha hz i hi
  dsimp only at hs
  apply cap1_impossible_of_duals bits k (lane width i beta) word
    (coeffs.map fun c => reconX rows (lane width i c)) hbits hword hoff
  · intro z hz
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hz
    exact hconstraint _ _ _ hword (hs.2.2 c hc) he
  · simpa [lane] using hs.1
  · simpa [lane] using hs.2.1

#print axioms cap1_raw_impossible
end PackedDigits

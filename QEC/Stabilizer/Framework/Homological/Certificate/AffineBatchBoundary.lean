import QEC.Stabilizer.Framework.Homological.Certificate.AffineMaskCheck
import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- A packed equality checks all boundary reconstructions and sheet joins in parallel. -/
theorem boundary_join_of_batch (width size coefficients sheets shadows : Nat)
    (G L R : List (Nat × Nat)) (hw : 0 < width)
    (hc : coefficients < 2^(width*size)) (hs : sheets < 2^(width*size))
    (hb : shadows < 2^(width*size))
    (hG : ∀ p ∈ G, p.1 < width ∧ p.2 < 2^width)
    (hL : ∀ p ∈ L, p.1 < width ∧ p.2 < 2^width)
    (hR : ∀ p ∈ R, p.1 < width ∧ p.2 < 2^width)
    (he : batchRecon (packF width size (fun _ => 1)) coefficients G =
      batchRecon (packF width size (fun _ => 1)) sheets L ^^^
        batchRecon (packF width size (fun _ => 1)) (sheets ^^^ shadows) R)
    {i : Nat} (hi : i < size) :
    reconX G (lane width i coefficients) =
      reconX L (lane width i sheets) ^^^
        reconX R (lane width i sheets ^^^ lane width i shadows) := by
  have hg := reconX_lane_of_batch width size coefficients _ G hw hc hG rfl hi
  have hl := reconX_lane_of_batch width size sheets _ L hw hs hL rfl hi
  have hr := reconX_lane_of_batch width size (sheets ^^^ shadows) _ R hw
    (Nat.xor_lt_two_pow hs hb) hR rfl hi
  rw [lane_xor] at hr
  rw [hg, he, lane_xor, ← hl, ← hr]

namespace AffineMaskCertificate

/-- Check that every reconstructed candidate indexes a common packed sheet table. -/
def checkIndexedBoundary (C : AffineMaskCertificate) (n width size sheets shadows : Nat)
    (E R : List (Nat × Nat)) : Bool :=
  affineColumnsCheck n C.beta E C.sectionColumns C.kernelColumns C.decoderColumns &&
    C.decoderColumns.all (fun p => decide (p.2 < 2 ^ C.dimension)) &&
    C.seeds.all (fun seed => (List.range (2 ^ C.dimension)).all (fun k =>
      let i := seed.2[k]!
      decide (i < size ∧ lane width i sheets = C.candidate E R seed.1 k ∧
        lane width i shadows = C.beta)))

/-- A shared packed boundary check covers every candidate in an indexed affine certificate. -/
theorem indexedBoundary_of_check (C : AffineMaskCertificate) (n width size sheets shadows : Nat)
    (E R G : List (Nat × Nat)) (join : Nat → Nat → Nat)
    (hb : ∀ i < size, ∃ coefficient,
      reconX G coefficient = join (lane width i sheets) (lane width i shadows))
    (h : C.checkIndexedBoundary n width size sheets shadows E R = true)
    {word : Nat} (hword : word < 2 ^ n)
    (hequation : reconX E word = reconX R C.beta)
    (hoff : outsideMask word C.beta ∈ C.seeds.map Prod.fst) :
    ∃ coefficient : Nat, reconX G coefficient = join word C.beta := by
  simp only [checkIndexedBoundary, Bool.and_eq_true] at h
  apply masked_affine_forall n C.beta (reconX R C.beta) C.dimension
    E C.sectionColumns C.kernelColumns C.decoderColumns
    (affineColumnsCheck_sound _ _ _ _ _ _ h.1.1)
    (fun p hp => of_decide_eq_true ((List.all_eq_true.mp h.1.2) p hp))
    (C.seeds.map Prod.fst) (fun v => ∃ coefficient, reconX G coefficient = join v C.beta)
    ?_ hword hequation hoff
  intro off ho k hk
  obtain ⟨seed, hs, rfl⟩ := List.mem_map.mp ho
  have hc := of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp h.2) seed hs)) k
    (List.mem_range.mpr hk))
  obtain ⟨coeff, he⟩ := hb _ hc.1
  exact ⟨coeff, by simpa only [hc.2.1, hc.2.2] using he⟩

end AffineMaskCertificate
#print axioms boundary_join_of_batch
#print axioms AffineMaskCertificate.indexedBoundary_of_check
end Quantum.Stabilizer.Homological.F2Mask

import QEC.Stabilizer.Framework.Homological.Certificate.AffineBatchBoundary

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- Check affine reconstruction using precomputed images of the point masses. -/
def affineColumnsCheckCached (n beta : Nat) (eColumn : Nat → Nat)
    (P K D : List (Nat × Nat)) : Bool :=
  (List.range n).all fun i => if beta.testBit i then
    Nat.beq (reconX P (eColumn i) ^^^ reconX K (reconX D (2 ^ i))) (2 ^ i)
  else true

/-- Correct point-mass images preserve the affine column check. -/
theorem affineColumnsCheckCached_eq (n beta : Nat) (eColumn : Nat → Nat)
    (E P K D : List (Nat × Nat))
    (he : ∀ i < n, eColumn i = reconX E (2 ^ i)) :
    affineColumnsCheckCached n beta eColumn P K D = affineColumnsCheck n beta E P K D := by
  apply Bool.eq_iff_iff.mpr
  simp only [affineColumnsCheckCached, affineColumnsCheck, List.all_eq_true]
  constructor <;> intro h i hi <;> have hc := h i hi
  · simpa only [he i (List.mem_range.mp hi)] using hc
  · simpa only [he i (List.mem_range.mp hi)] using hc

namespace AffineMaskCertificate
/-- The indexed affine check with shared point-mass images. -/
def checkIndexedBoundaryCached (C : AffineMaskCertificate)
    (n width size sheets shadows rhs : Nat) (eColumn : Nat → Nat)
    (E _R : List (Nat × Nat)) : Bool :=
  affineColumnsCheckCached n C.beta eColumn C.sectionColumns C.kernelColumns C.decoderColumns &&
    C.decoderColumns.all (fun p => decide (p.2 < 2 ^ C.dimension)) &&
    C.seeds.all (fun seed => (List.range (2 ^ C.dimension)).all (fun k =>
      let i := seed.2[k]!
      decide (i < size ∧ lane width i sheets = seed.1 ^^^
        reconX C.sectionColumns (rhs ^^^ reconX E seed.1) ^^^ reconX C.kernelColumns k ∧
        lane width i shadows = C.beta)))

/-- Caching the common linear-map columns does not change the indexed checker. -/
theorem checkIndexedBoundaryCached_eq (C : AffineMaskCertificate)
    (n width size sheets shadows rhs : Nat) (eColumn : Nat → Nat)
    (E R : List (Nat × Nat))
    (he : ∀ i < n, eColumn i = reconX E (2 ^ i))
    (hr : rhs = reconX R C.beta) :
    C.checkIndexedBoundaryCached n width size sheets shadows rhs eColumn E R =
      C.checkIndexedBoundary n width size sheets shadows E R := by
  unfold checkIndexedBoundaryCached checkIndexedBoundary candidate
  rw [hr, affineColumnsCheckCached_eq n C.beta eColumn E C.sectionColumns C.kernelColumns C.decoderColumns he]
end AffineMaskCertificate
end Quantum.Stabilizer.Homological.F2Mask

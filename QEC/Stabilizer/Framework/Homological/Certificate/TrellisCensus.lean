import QEC.Stabilizer.Framework.Homological.Certificate.PackedProgram
import QEC.Stabilizer.Framework.Homological.WeightCensus

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis.PackedProgram

/-- A kernel-evaluated packed trellis bounds every finite collection that its encoder covers. -/
theorem card_le_of_compute {slot degree : Nat} (C : PackedProgram slot degree 0 0)
    (target : Finset Nat) (answer : Nat)
    (hs : 0 < slot) (hbudget : 2 ^ C.merges < 2 ^ slot)
    (hinputs : 2 ^ reads C.certificate.program < 2 ^ slot - 1)
    (hcover : ∀ word ∈ target, ∃ input < 2 ^ reads C.certificate.program,
      runWord C.certificate.program input 0 = word)
    (hlight : ∀ word ∈ target, bitCount (outputs C.certificate.program) word ≤ degree)
    (hcompute : C.numeric 1 = answer)
    (hanswer : answer < 2 ^ (slot * (degree + 1))) :
    target.card ≤ answer % (2 ^ slot - 1) := by
  apply card_le_of_weight_sum (Finset.range (2 ^ reads C.certificate.program)) target
    (fun input => runWord C.certificate.program input 0)
    (bitCount (outputs C.certificate.program)) (2 ^ slot) degree answer
  · exact Nat.one_lt_two_pow (by omega)
  · simpa using hinputs
  · intro word hw
    obtain ⟨input, hi, heq⟩ := hcover word hw
    exact ⟨input, Finset.mem_range.mpr hi, heq⟩
  · exact hlight
  · have h := C.closed_eq_sum hs hbudget
    rw [hcompute] at h
    have hcast : ((∑ input ∈ Finset.range (2 ^ reads C.certificate.program),
        (2 ^ slot : Nat) ^ bitCount (outputs C.certificate.program)
          (runWord C.certificate.program input 0) : Nat) : WeightRing slot degree) =
        (answer : WeightRing slot degree) := by
      simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using h.symm
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    rw [Nat.mod_eq_of_lt hanswer] at hm
    simpa only [Nat.pow_mul] using hm

end Quantum.Stabilizer.Homological.F2Mask.Trellis.PackedProgram

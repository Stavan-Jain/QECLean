import QEC.Stabilizer.Framework.Homological.Certificate.TrellisCensus

namespace Quantum.Stabilizer.Homological.F2Mask.Trellis

/-- Finite checks on basis inputs cover an entire affine coset of their XOR-span. -/
theorem affine_span_covered (program : List Instruction) (checks : List (Nat × Nat))
    (offset : Nat)
    (hzero : runWord program 0 0 = offset)
    (hchecks : checks.all (fun gi => decide (gi.2 < 2 ^ reads program) &&
      decide (runWord program gi.2 0 = gi.1 ^^^ offset)) = true)
    {word : Nat} (hspan : XorSpan (checks.map Prod.fst) (word ^^^ offset)) :
    ∃ input < 2 ^ reads program, runWord program input 0 = word := by
  have hgen : ∀ g ∈ checks.map Prod.fst, ∃ input < 2 ^ reads program,
      runWord program input 0 = g ^^^ runWord program 0 0 := by
    intro g hg
    obtain ⟨gi, hgi, rfl⟩ := List.mem_map.mp hg
    have hc := (List.all_eq_true.mp hchecks) gi hgi
    have hh := Bool.and_eq_true_iff.mp hc
    refine ⟨gi.2, of_decide_eq_true hh.1, ?_⟩
    simpa only [hzero] using of_decide_eq_true hh.2
  obtain ⟨input, hi, heq⟩ := xorSpan_mem_affine_image
    (fun input => runWord program input 0) (reads program)
    (runWord_affine program) (checks.map Prod.fst) hgen hspan
  exact ⟨input, hi, by simpa [hzero, Nat.xor_assoc] using heq⟩

/-- A computed packed encoder bounds any collection in its certified affine generator span. -/
theorem PackedProgram.card_le_of_span_compute {slot degree : Nat}
    (C : PackedProgram slot degree 0 0) (checks : List (Nat × Nat))
    (offset : Nat) (target : Finset Nat) (answer : Nat)
    (hs : 0 < slot) (hbudget : 2 ^ C.merges < 2 ^ slot)
    (hinputs : 2 ^ reads C.certificate.program < 2 ^ slot - 1)
    (hzero : runWord C.certificate.program 0 0 = offset)
    (hchecks : checks.all (fun gi => decide (gi.2 < 2 ^ reads C.certificate.program) &&
      decide (runWord C.certificate.program gi.2 0 = gi.1 ^^^ offset)) = true)
    (hspan : ∀ word ∈ target, XorSpan (checks.map Prod.fst) (word ^^^ offset))
    (hlight : ∀ word ∈ target, bitCount (outputs C.certificate.program) word ≤ degree)
    (hcompute : C.numeric 1 = answer)
    (hanswer : answer < 2 ^ (slot * (degree + 1))) :
    target.card ≤ answer % (2 ^ slot - 1) := by
  exact C.card_le_of_compute target answer hs hbudget hinputs
    (fun word hw => affine_span_covered _ _ _ hzero hchecks (hspan word hw))
    hlight hcompute hanswer

#print axioms PackedProgram.card_le_of_span_compute
end Quantum.Stabilizer.Homological.F2Mask.Trellis

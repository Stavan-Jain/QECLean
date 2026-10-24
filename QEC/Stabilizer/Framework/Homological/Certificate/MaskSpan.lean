import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Decoding an XOR span preserves membership in any binary subspace containing its generators. -/
theorem XorSpan.chainOfMask_mem {ι : Type} {n : Nat} (e : ι ≃ Fin n)
    (S : Submodule (ZMod 2) (ι → ZMod 2)) {gens : List Nat} {m : Nat}
    (h : XorSpan gens m) (hgens : ∀ g ∈ gens, chainOfMask e g ∈ S) :
    chainOfMask e m ∈ S := by
  induction h with
  | zero => rw [chainOfMask_zero]; exact S.zero_mem
  | step hg _ ih => rw [chainOfMask_xor]; exact S.add_mem (hgens _ hg) ih

/-- A reconstruction from masks in a subspace remains in that subspace. -/
theorem chainOfMask_reconX_mem {ι : Type} {n : Nat} (e : ι ≃ Fin n)
    (S : Submodule (ZMod 2) (ι → ZMod 2)) (cols : List (Nat × Nat))
    (hcols : ∀ p ∈ cols, chainOfMask e p.2 ∈ S) (coeff : Nat) :
    chainOfMask e (reconX cols coeff) ∈ S := by
  apply (reconX_mem_span cols coeff).chainOfMask_mem e S
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  exact hcols p hp

end Quantum.Stabilizer.Homological.F2Mask

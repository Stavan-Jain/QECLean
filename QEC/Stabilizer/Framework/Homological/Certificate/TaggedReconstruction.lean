import QEC.Stabilizer.Framework.Homological.Certificate.ReconComposition

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A syndrome tag leaves the bounded word in its low coordinates. -/
theorem low_tag (n word syndrome : Nat) (hw : word < 2^n) :
    (word ^^^ (syndrome <<< n)) &&& (2^n-1) = word := by
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.xor_mod_two_pow,Nat.mod_eq_of_lt hw,
    Nat.shiftLeft_eq,Nat.mul_mod_left,Nat.xor_zero]

/-- A syndrome tag places its syndrome in the high coordinates. -/
theorem high_tag (n word syndrome : Nat) (hw : word < 2^n) :
    (word ^^^ (syndrome <<< n)) >>> n = syndrome := by
  rw [Nat.shiftRight_xor_distrib,Nat.shiftRight_eq_div_pow,Nat.div_eq_of_lt hw,Nat.zero_xor,
    Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,Nat.mul_div_cancel]
  exact Nat.two_pow_pos n

/-- Tagged columns reconstruct the word and its exact full syndrome together. -/
theorem tagged_reconstruction (n : Nat) (E rows : List (Nat × Nat)) (coeff word : Nat)
    (hcolumns : ∀ p ∈ rows, reconX E (p.2 &&& (2^n-1)) = p.2 >>> n)
    (hlow : reconX (rows.map fun p => (p.1,p.2 &&& (2^n-1))) coeff = word) :
    (reconX rows coeff &&& (2^n-1) = word) ∧
      (reconX rows coeff >>> n = reconX E word) := by
  refine ⟨by rw [reconX_and,hlow],?_⟩
  rw [reconX_shiftRight,← hlow,reconX_comp,List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [hcolumns p hp]

#print axioms tagged_reconstruction
end Quantum.Stabilizer.Homological.F2Mask

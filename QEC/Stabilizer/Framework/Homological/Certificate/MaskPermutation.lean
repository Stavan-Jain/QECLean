import QEC.Stabilizer.Framework.Homological.Certificate.KernelSpan

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Column checks identify a reconstruction with coordinate reindexing. -/
theorem reconX_eq_reindex {n : Nat} (e : Fin n ≃ Fin n) (window : List (Nat × Nat))
    (hcolumns : ∀ i : Fin n, reconX window (2 ^ i.val) = 2 ^ (e i).val)
    {word : Nat} (hword : word < 2 ^ n) :
    reconX window word = maskOf e (chainOfMask (Equiv.refl (Fin n)) word) := by
  apply xor_map_eq_of_basis (reconX window)
    (fun word => maskOf e (chainOfMask (Equiv.refl (Fin n)) word)) n
    (reconX_zero window) ?_ (reconX_xor window) ?_ ?_ word hword
  · simp [chainOfMask_zero, maskOf_zero]
  · intro a b
    dsimp only
    rw [chainOfMask_xor, maskOf_add]
  · intro i hi
    rw [hcolumns ⟨i, hi⟩]
    change 2 ^ (e ⟨i, hi⟩).val =
      maskOf e (chainOfMask (Equiv.refl (Fin n)) (2 ^ ((Equiv.refl (Fin n)) ⟨i, hi⟩).val))
    rw [chainOfMask_two_pow, maskOf_single]

/-- A checked coordinate permutation preserves the number of set bits. -/
theorem reconX_permutation_weight {n : Nat} (e : Fin n ≃ Fin n) (window : List (Nat × Nat))
    (hcolumns : ∀ i : Fin n, reconX window (2 ^ i.val) = 2 ^ (e i).val)
    {word : Nat} (hword : word < 2 ^ n) :
    bitCount n (reconX window word) = bitCount n word := by
  rw [reconX_eq_reindex e window hcolumns hword,
    ← card_support_eq_bitCount e, card_support_eq_bitCount (Equiv.refl (Fin n)),
    maskOf_chainOfMask _ hword]

/-- A checked coordinate permutation is injective on the bounded mask space. -/
theorem reconX_permutation_injective {n : Nat} (e : Fin n ≃ Fin n) (window : List (Nat × Nat))
    (hcolumns : ∀ i : Fin n, reconX window (2 ^ i.val) = 2 ^ (e i).val)
    {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (heq : reconX window a = reconX window b) : a = b := by
  rw [reconX_eq_reindex e window hcolumns ha, reconX_eq_reindex e window hcolumns hb] at heq
  have hc := maskOf_injective e heq
  have hm := congrArg (maskOf (Equiv.refl (Fin n))) hc
  simpa only [maskOf_chainOfMask _ ha, maskOf_chainOfMask _ hb] using hm

#print axioms reconX_permutation_weight
#print axioms reconX_permutation_injective
end Quantum.Stabilizer.Homological.F2Mask

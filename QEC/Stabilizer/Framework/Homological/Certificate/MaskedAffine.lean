import QEC.Stabilizer.Framework.Homological.Certificate.KernelSpan

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Checked point-mass identities reconstruct the part of any mask inside a fixed support. -/
theorem masked_affine_reconstruct (n beta : Nat) (E P K D : List (Nat × Nat))
    (hcolumns : (List.range n).all (fun i => decide
      (reconX P (reconX E ((2 ^ i) &&& beta)) ^^^
        reconX K (reconX D ((2 ^ i) &&& beta)) = (2 ^ i) &&& beta)) = true)
    {word : Nat} (hword : word < 2 ^ n) :
    reconX P (reconX E (word &&& beta)) ^^^ reconX K (reconX D (word &&& beta)) =
      word &&& beta := by
  apply xor_map_eq_of_basis
    (fun x => reconX P (reconX E (x &&& beta)) ^^^ reconX K (reconX D (x &&& beta)))
    (fun x => x &&& beta) n
    (by simp [reconX_zero]) (by simp) ?_ (fun _ _ => Nat.and_xor_distrib_right) ?_ word hword
  · intro a b
    simp only [Nat.and_xor_distrib_right, reconX_xor]
    ac_rfl
  · intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp hcolumns) i (List.mem_range.mpr hi))

/-- The support outside a fixed mask is the XOR complement of its part inside. -/
def outsideMask (word beta : Nat) : Nat := word ^^^ (word &&& beta)

/-- Every affine solution is its outside support plus a certified particular and free part. -/
theorem masked_affine_solution (n beta rhs : Nat) (E P K D : List (Nat × Nat))
    (hcolumns : (List.range n).all (fun i => decide
      (reconX P (reconX E ((2 ^ i) &&& beta)) ^^^
        reconX K (reconX D ((2 ^ i) &&& beta)) = (2 ^ i) &&& beta)) = true)
    {word : Nat} (hword : word < 2 ^ n) (hequation : reconX E word = rhs) :
    word = outsideMask word beta ^^^
      reconX P (rhs ^^^ reconX E (outsideMask word beta)) ^^^
        reconX K (reconX D (word &&& beta)) := by
  have he : rhs ^^^ reconX E (outsideMask word beta) = reconX E (word &&& beta) := by
    rw [outsideMask, reconX_xor, hequation]
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [he, Nat.xor_assoc, masked_affine_reconstruct n beta E P K D hcolumns hword,
    outsideMask, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Finite checks of all particular-plus-free candidates cover every affine solution. -/
theorem masked_affine_forall (n beta rhs dimension : Nat) (E P K D : List (Nat × Nat))
    (hcolumns : (List.range n).all (fun i => decide
      (reconX P (reconX E ((2 ^ i) &&& beta)) ^^^
        reconX K (reconX D ((2 ^ i) &&& beta)) = (2 ^ i) &&& beta)) = true)
    (hD : ∀ p ∈ D, p.2 < 2 ^ dimension)
    (census : List Nat) (property : Nat → Prop)
    (hchecks : ∀ off ∈ census, ∀ k < 2 ^ dimension,
      property (off ^^^ reconX P (rhs ^^^ reconX E off) ^^^ reconX K k))
    {word : Nat} (hword : word < 2 ^ n) (hequation : reconX E word = rhs)
    (hoff : outsideMask word beta ∈ census) : property word := by
  rw [masked_affine_solution n beta rhs E P K D hcolumns hword hequation]
  exact hchecks _ hoff _ (reconX_lt D _ dimension hD)

#print axioms masked_affine_forall
end Quantum.Stabilizer.Homological.F2Mask

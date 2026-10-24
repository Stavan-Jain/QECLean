import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial

namespace Quantum.Stabilizer.Homological.F2Mask
open PackedDigits

/-- Check packed dual neighborhoods, their target parities, and their shadow annihilation. -/
def checkSearchInitial (k n size rows lambdas target beta rhs : Nat)
    (T : List (Nat × Nat)) : Bool :=
  decide (rows < 2^((2^k)*size) ∧ lambdas < 2^((2^k)*size) ∧ target < 2^size) &&
    Nat.beq (batchRecon (packF (2^k) size (fun _ => 1)) lambdas T) rows &&
    (List.range size).all (fun i => decide (
      lane (2^k) i lambdas < 2^n ∧ lane (2^k) i rows &&& beta = 0 ∧
      parityFold k (lane (2^k) i lambdas &&& rhs) = if target.testBit i then 1 else 0))

/-- A checked dual table and search tree give a complete outside-support census. -/
theorem outside_mem_of_search (k n size rows lambdas target beta rhs cap : Nat)
    (E T : List (Nat × Nat)) (tree : ParitySearchTree) (census : List Nat)
    (hn : n ≤ 2^k)
    (htranspose : ∀ lam word, lam < 2^n → word < 2^n →
      parityFold k (reconX T lam &&& word) = parityFold k (lam &&& reconX E word))
    (hT : ∀ p ∈ T, p.1 < 2^k ∧ p.2 < 2^(2^k))
    (hi : checkSearchInitial k n size rows lambdas target beta rhs T = true)
    (ht : checkParitySearch k (fun i => lane (2^k) i rows) target census.contains tree
      ((2^n-1) ^^^ beta) 0 cap = true)
    {word : Nat} (hw : word < 2^n) (he : reconX E word = rhs)
    (hweight : bitCount n (outsideMask word beta) ≤ cap) :
    outsideMask word beta ∈ census := by
  simp only [checkSearchInitial, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq,
    List.all_eq_true] at hi
  have hs := packed_search_constraints k n size rows lambdas target beta rhs E T
    htranspose hT hi.1.1.1 hi.1.1.2.1 hi.1.1.2.2 hi.1.2
    (fun i hir => hi.2 i (List.mem_range.mpr hir)) hw he
  have hoff : outsideMask word beta < 2^n := by
    rw [outsideMask_eq_and_complement hw]
    exact lt_of_le_of_lt Nat.and_le_left hw
  apply List.contains_iff_mem.mp
  apply checkParitySearch_complete k (fun i => lane (2^k) i rows) target census.contains
    tree ((2^n-1) ^^^ beta) cap ht
    (hoff.trans_le (Nat.pow_le_pow_right (by decide) hn)) hs
    (outsideMask_support_subset hw)
  rwa [bitCount_eq_of_bound hn hoff]

#print axioms outside_mem_of_search
end Quantum.Stabilizer.Homological.F2Mask

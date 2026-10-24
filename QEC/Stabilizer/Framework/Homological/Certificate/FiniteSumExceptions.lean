import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace Quantum.Stabilizer.Homological

/-- A finite function with a constant default is counted by its exceptional values. -/
theorem sum_of_exceptional_values {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Nat) (exceptions : Finset ι) (default total count special : Nat)
    (htotal : Fintype.card ι = total) (hcount : exceptions.card = count)
    (hspecial : ∑ i ∈ exceptions, f i = special)
    (hdefault : ∀ i, i ∉ exceptions → f i = default) :
    (∑ i, f i) = (total-count)*default+special := by
  have hsplit := Finset.sum_sdiff (Finset.subset_univ exceptions) (f := f)
  have hrest : (∑ i ∈ Finset.univ \ exceptions, f i) = (total-count)*default := by
    calc
      _ = (Finset.univ \ exceptions).card * default := by
        apply Finset.sum_const_nat
        intro i hi
        exact hdefault i (Finset.mem_sdiff.mp hi).2
      _ = (total-count)*default := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ exceptions),
          Finset.card_univ, htotal, hcount]
  omega

end Quantum.Stabilizer.Homological

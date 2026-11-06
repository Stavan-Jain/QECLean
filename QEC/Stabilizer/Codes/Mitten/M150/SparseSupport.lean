import QEC.Stabilizer.Codes.Mitten.M150.Sparse

namespace Quantum.Stabilizer.Homological.LP.M150
open scoped BigOperators

/-- The indicator chain of an explicitly listed qubit support. -/
def supportChain (support : List Nat) : Fin 5 × M150G → ZMod 2 :=
  fun q => if q ∈ support.map qubitOf then 1 else 0

/-- An indicator chain is the sum of the point masses on its support. -/
lemma supportChain_eq_sum (support : List Nat) :
    supportChain support = ∑ q ∈ (support.map qubitOf).toFinset, Pi.single q (1 : ZMod 2) := by
  funext q
  simp [supportChain, Finset.sum_apply, Pi.single_apply]

/-- The primal syndrome of a sparse support sums only its nonzero entries. -/
lemma boundary1_supportChain (support : List Nat) (p : m150Complex.C0) :
    m150Complex.boundary1 (supportChain support) p =
      ∑ q ∈ (support.map qubitOf).toFinset, cmTerm p q := by
  rw [supportChain_eq_sum]
  have h := map_sum m150Complex.boundary1
    (fun q : m150Complex.C1 => Pi.single q (1 : ZMod 2))
    (support.map qubitOf).toFinset
  have hp := congrFun h p
  simpa only [Finset.sum_apply, boundary1_single_apply] using hp

/-- The dual syndrome of a point mass is its sparse check-matrix column. -/
lemma dualBoundary_single_apply (q : m150Complex.C1) (p : m150Complex.C2) :
    m150Complex.dualBoundary (Pi.single q 1) p = d2term p q := by
  rw [dualBoundary_eq_dualBfn]
  simp only [dualBfn, Pi.single_apply, ite_mul, one_mul, zero_mul]
  simpa only [Finset.mem_univ, if_true] using
    Finset.sum_ite_eq' Finset.univ q (d2term p)

/-- The dual syndrome of a sparse support sums only its nonzero entries. -/
lemma dualBoundary_supportChain (support : List Nat) (p : m150Complex.C2) :
    m150Complex.dualBoundary (supportChain support) p =
      ∑ q ∈ (support.map qubitOf).toFinset, d2term p q := by
  rw [supportChain_eq_sum]
  have h := map_sum m150Complex.dualBoundary
    (fun q : m150Complex.C1 => Pi.single q (1 : ZMod 2))
    (support.map qubitOf).toFinset
  have hp := congrFun h p
  simpa only [Finset.sum_apply, dualBoundary_single_apply] using hp

/-- Pairing with a sparse chain only visits its support. -/
lemma supportChain_pairing (support : List Nat) (c : m150Complex.C1 → ZMod 2) :
    (∑ q, supportChain support q * c q) =
      ∑ q ∈ (support.map qubitOf).toFinset, c q := by
  simp only [supportChain, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext q
  simp

end Quantum.Stabilizer.Homological.LP.M150

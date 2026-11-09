import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix

/-!
# Decidability of `rowsLinearIndependent`

For a list `L` of n-qubit Pauli group elements, `rowsLinearIndependent L` says
that the only `ZMod 2`-combination of the check-matrix rows that vanishes is the
trivial one. The `Decidable` instance checks every coefficient vector
`f : Fin L.length → ZMod 2`.

That is `2 ^ L.length` cases: fine for small codes, but out of reach for large
ones (roughly more than 20 rows). There, use the polynomial-time certificate
`rowsLinearIndependent_of_rankCertCheck` instead.
-/

namespace Quantum

variable {n : ℕ}

open scoped BigOperators

namespace NQubitPauliGroupElement

/-- The rows are linearly independent iff the only coefficient vector giving the
zero combination is the zero vector. -/
theorem rowsLinearIndependent_iff_forall (L : List (NQubitPauliGroupElement n)) :
    rowsLinearIndependent L ↔
      ∀ f : Fin L.length → ZMod 2, (∑ i, f i • checkMatrix L i) = 0 → f = 0 := by
  simp only [rowsLinearIndependent, Fintype.linearIndependent_iff, funext_iff, Pi.zero_apply]

/-- Row linear independence is decidable, by checking every coefficient vector
in `(ZMod 2) ^ L.length`. -/
instance (L : List (NQubitPauliGroupElement n)) : Decidable (rowsLinearIndependent L) :=
  decidable_of_iff' (∀ f : Fin L.length → ZMod 2, (∑ i, f i • checkMatrix L i) = 0 → f = 0)
    (rowsLinearIndependent_iff_forall L)

end NQubitPauliGroupElement

end Quantum

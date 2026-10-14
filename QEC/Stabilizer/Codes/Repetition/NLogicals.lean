import QEC.Stabilizer.Codes.Repetition.N

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace RepetitionCodeN

/-!
# The repetition code on `n + 2` qubits: logical operators

The logical basis of `RepetitionCodeN.stabilizerCode n`: transversal
`X̄ = X⊗ⁿ⁺²` and `Z̄ = Z⊗ⁿ⁺²`. Both commute with every check (`X̄` meets each
`ZZ` on two qubits, `Z̄` is Z-type), but they anticommute only when the number
of physical qubits `n + 2` is odd, so the logical basis
(`stabilizerCodeWithLogicals`) is defined only for odd `n + 2`. The bare code,
and its distance, exist for every `n`.

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ` (for odd `n + 2`)
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[n+2, 1]]ₗ` (for odd `n + 2`)
-/

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X: X on all `n+2` qubits. -/
def logicalX (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.X (n + 2)⟩

/-- Logical Z: Z on all `n+2` qubits. -/
def logicalZ (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.Z (n + 2)⟩

/-! ## Anticommutation -/

/-- `X̄` and `Z̄` anticommute when the number of physical qubits `n+2` is
odd. -/
theorem logicalX_anticommutes_logicalZ (n : ℕ) (hn : Odd (n + 2)) :
    Anticommute (logicalX n) (logicalZ n) :=
  NQubitPauliOperator.allX_allZ_anticommute (n + 2) hn

/-! ## Centralizer membership

`X̄ = X⊗ⁿ⁺²` is the partner of the distance witness in `N.lean`, whose
centralizer membership is already proved there. `Z̄` is Z-type, so it commutes
with every check componentwise. -/

/-- `X̄` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer (n : ℕ) : logicalX n ∈ centralizer (stabilizerGroup n) :=
  minWeightPartner_mem_centralizer n

private lemma logicalZ_commutes_ZPair (n : ℕ) (i : Fin (n + 1)) :
    logicalZ n * ZPair n i = ZPair n i * logicalZ n := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro j
  by_cases hj1 : j = Fin.castSucc i <;> by_cases hj2 : j = Fin.succ i
  · subst hj1; grind
  · subst hj1
    simp only [logicalZ, NQubitPauliOperator.Z, ZPair, NQubitPauliOperator.set,
      ↓reduceIte, ite_self]
  · subst hj2
    simp only [logicalZ, NQubitPauliOperator.Z, ZPair, NQubitPauliOperator.set,
      ↓reduceIte]
  · simp only [logicalZ, NQubitPauliOperator.Z, ZPair, NQubitPauliOperator.set,
    NQubitPauliOperator.identity, if_neg hj1, if_neg hj2, PauliOperator.mulOp_Z_I,
    PauliOperator.mulOp_I_Z]

/-- `Z̄` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer (n : ℕ) :
    logicalZ n ∈ centralizer (stabilizerGroup n) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure (logicalZ n) (stabilizerGroup n) (generators n)
    (stabilizerGroup_toSubgroup_eq n)]
  intro s hs
  simp only [generators, XGenerators, Set.mem_union, Set.mem_empty_iff_false] at hs
  rcases hs with ⟨i, rfl⟩ | hEmp
  · exact (logicalZ_commutes_ZPair n i).symm
  · exact False.elim hEmp

/-! ## The code with its logical basis `Code[[n+2, 1]]ₗ` (odd `n + 2`) -/

/-- The single logical qubit `(X̄, Z̄)`, for odd `n + 2`. -/
private def logicalOpsRepN (n : ℕ) (hn : Odd (n + 2)) :
    Fin 1 → LogicalQubitOps (n + 2) (stabilizerGroup n) :=
  fun _ => ⟨logicalX n, logicalZ n, logicalX_mem_centralizer n, logicalZ_mem_centralizer n,
    logicalX_anticommutes_logicalZ n hn⟩

/-- The repetition code on `n + 2` qubits with its logical basis
`X̄ = X⊗ⁿ⁺²`, `Z̄ = Z⊗ⁿ⁺²`, which anticommute exactly when `n + 2` is odd. -/
noncomputable def stabilizerCodeWithLogicals (n : ℕ) (hn : Odd (n + 2)) :
    Code[[n + 2, 1]]ₗ where
  toStabilizerCode := stabilizerCode n
  logicalOps := logicalOpsRepN n hn
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end RepetitionCodeN
end StabilizerGroup

end Quantum

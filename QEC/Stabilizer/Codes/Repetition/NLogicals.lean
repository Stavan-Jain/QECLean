import QEC.Stabilizer.Codes.Repetition.N

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

namespace Quantum
namespace StabilizerGroup
namespace RepetitionCodeN

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X: X on all `n + 2` qubits. -/
def logicalX (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.X (n + 2)⟩

/-- Logical Z: Z on all `n + 2` qubits. -/
def logicalZ (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.Z (n + 2)⟩

/-! ## Anticommutation -/

/-- `X̄ = X⊗ⁿ⁺²` and `Z̄ = Z⊗ⁿ⁺²` anticommute when `n + 2` is odd: they meet on
all `n + 2` qubits. -/
lemma logicalX_anticommutes_logicalZ (n : ℕ) (hn : Odd (n + 2)) :
    Anticommute (logicalX n) (logicalZ n) :=
  NQubitPauliOperator.allX_allZ_anticommute (n + 2) hn

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the generators.
`X̄ = X⊗ⁿ⁺²` is the partner of the distance witness in `N.lean`, and `Z̄` is
Z-type, as every check is. -/

/-- `X̄ = X⊗ⁿ⁺²` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer (n : ℕ) : logicalX n ∈ centralizer (stabilizerGroup n) :=
  minWeightPartner_mem_centralizer n

/-- `Z̄ = Z⊗ⁿ⁺²` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer (n : ℕ) : logicalZ n ∈ centralizer (stabilizerGroup n) :=
  (mem_centralizer_iff_closure _ _ (generators n) (stabilizerGroup_toSubgroup_eq n)).mpr
    fun s hs => (generators_isZType n s hs).commute ⟨rfl, fun _ => Or.inr rfl⟩

/-! ## The code with its logical basis `Code[[n+2, 1]]ₗ` -/

/-- The repetition code on `n + 2` qubits with its logical basis
`X̄ = X⊗ⁿ⁺²`, `Z̄ = Z⊗ⁿ⁺²`, for odd `n + 2`. -/
noncomputable def stabilizerCodeWithLogicals (n : ℕ) (hn : Odd (n + 2)) : Code[[n + 2, 1]]ₗ where
  toStabilizerCode := stabilizerCode n
  logicalOps _ := ⟨logicalX n, logicalZ n, logicalX_mem_centralizer n, logicalZ_mem_centralizer n,
    logicalX_anticommutes_logicalZ n hn⟩
  logical_commute_cross ℓ ℓ' h := (h (Subsingleton.elim ℓ ℓ')).elim

end RepetitionCodeN
end StabilizerGroup
end Quantum

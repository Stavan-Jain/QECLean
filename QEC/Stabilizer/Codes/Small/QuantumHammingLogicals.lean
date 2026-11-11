import QEC.Stabilizer.Codes.Small.QuantumHamming

/-!
# Quantum Hamming codes: logical operators

The transversal logical pair of `QuantumHamming.stabilizerCode`:
`X̄ = X⊗ⁿ` and `Z̄ = Z⊗ⁿ` on all `n = 2^r − 1` qubits. Each commutes with every
check (a Hamming row has `2^(r−1)` qubits, an even number) and they anticommute
with each other (`2^r − 1` is odd).

This is one pair out of the `2^r − 1 − 2r` logical qubits, so no
`StabilizerCodeWithLogicals` is bundled here; a full basis needs a basis of the
classical Hamming code modulo its dual. For `r = 3`, the Steane code, the one
pair is the whole basis: see `Steane7Logicals.lean`.

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
-/

namespace Quantum
namespace StabilizerGroup
namespace QuantumHamming

open NQubitPauliGroupElement
open scoped Pauli

variable (r : ℕ)

/-! ## Logical operators -/

/-- Logical X: X on all `2^r − 1` qubits. -/
def logicalX : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, NQubitPauliOperator.X (2 ^ r - 1)⟩

/-- Logical Z: Z on all `2^r − 1` qubits. -/
def logicalZ : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, NQubitPauliOperator.Z (2 ^ r - 1)⟩

/-- `X̄` is `X` on the support of all qubits. -/
lemma logicalX_eq_xOn : logicalX r = xOn Finset.univ :=
  xOn_univ.symm

/-- `Z̄` is `Z` on the support of all qubits. -/
lemma logicalZ_eq_zOn : logicalZ r = zOn Finset.univ :=
  zOn_univ.symm

/-! ## Anticommutation -/

/-- `2^r − 1` is odd for `r ≥ 1`. -/
lemma two_pow_sub_one_odd (hr1 : 1 ≤ r) : Odd (2 ^ r - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one

/-- `X̄ = X⊗ⁿ` and `Z̄ = Z⊗ⁿ` anticommute: they meet on all `n = 2^r − 1`
qubits, an odd number. -/
lemma logicalX_anticommutes_logicalZ (hr1 : 1 ≤ r) : Anticommute (logicalX r) (logicalZ r) :=
  NQubitPauliOperator.allX_allZ_anticommute (2 ^ r - 1) (two_pow_sub_one_odd r hr1)

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the generators. The
support of `X̄` and `Z̄`, all the qubits, meets each Hamming row in the row
itself, an even number of qubits, so `xOn_mem_centralizer` and
`zOn_mem_centralizer` apply. -/

/-- `X̄ = X⊗ⁿ` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer (hr : 3 ≤ r) : logicalX r ∈ centralizer (stabilizerGroup r hr) :=
  logicalX_eq_xOn r ▸
    xOn_mem_centralizer r hr fun a => (Finset.univ_inter (row r a)).symm ▸ even_card_row r hr a

/-- `Z̄ = Z⊗ⁿ` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer (hr : 3 ≤ r) : logicalZ r ∈ centralizer (stabilizerGroup r hr) :=
  logicalZ_eq_zOn r ▸
    zOn_mem_centralizer r hr fun a => (Finset.univ_inter (row r a)).symm ▸ even_card_row r hr a

end QuantumHamming
end StabilizerGroup
end Quantum

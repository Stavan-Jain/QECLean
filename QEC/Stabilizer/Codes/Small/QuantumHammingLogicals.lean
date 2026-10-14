import QEC.Stabilizer.Codes.Small.QuantumHamming

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace QuantumHamming

/-!
# Quantum Hamming codes: logical operators

The transversal logical pair of `QuantumHamming.stabilizerCode`:
`X̄ = X⊗ⁿ` and `Z̄ = Z⊗ⁿ` on all `n = 2^r − 1` qubits. Each commutes with every
check (a Hamming row has `2^(r−1)` ones, an even number) and they anticommute
with each other (`2^r − 1` is odd).

This is one logical qubit pair. The full set of `2^r − 1 − 2r` pairs requires
the codeword structure of the underlying Hamming code, so no
`StabilizerCodeWithLogicals` is bundled here (for `r = 3`, the Steane code, the
one pair is the whole basis — see `Steane7Logicals.lean`).

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
-/

open NQubitPauliGroupElement

variable (r : ℕ)

/-! ## Logical operators -/

/-- Logical X: X on all `2^r − 1` qubits. -/
def logicalX : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, NQubitPauliOperator.X (2 ^ r - 1)⟩

/-- Logical Z: Z on all `2^r − 1` qubits. -/
def logicalZ : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, NQubitPauliOperator.Z (2 ^ r - 1)⟩

/-! ## Anticommutation -/

/-- `2^r − 1` is odd for `r ≥ 1`. -/
lemma two_pow_sub_one_odd (hr1 : 1 ≤ r) : Odd (2 ^ r - 1) := by
  rw [Nat.odd_sub (Nat.one_le_two_pow)]
  simp [Nat.even_pow]
  omega

/-- Logical X and logical Z anticommute (`2^r − 1` is odd). -/
theorem logicalX_anticommutes_logicalZ (hr1 : 1 ≤ r) :
    Anticommute (logicalX r) (logicalZ r) :=
  NQubitPauliOperator.allX_allZ_anticommute (2 ^ r - 1) (two_pow_sub_one_odd r hr1)

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the generators. `X̄`
commutes with each X-generator componentwise, and meets each Z-generator in the
`2^(r−1)` ones of a Hamming row, an even number; dually for `Z̄`. -/

/-- Logical X commutes with every Z-generator (each Z-row has `2^(r−1)` ones,
which is even). -/
private lemma logicalX_commutes_ZGen (hr : 3 ≤ r) (a : Fin r) :
    logicalX r * ZGen r a = ZGen r a * logicalX r := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero]
  have key : (logicalX r).operators.symplecticInner
      (ZGen r a).operators = hammingRowDot r a a := by
    simp only [NQubitPauliOperator.symplecticInner, logicalX, ZGen,
      NQubitPauliOperator.X, hammingRowDot, hammingEntry,
      PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle]
    congr 1; ext k; split_ifs <;> simp
  rw [key]; exact hammingRowDot_eq_zero r hr a a

/-- Logical Z commutes with every X-generator (same even-overlap argument). -/
private lemma logicalZ_commutes_XGen (hr : 3 ≤ r) (a : Fin r) :
    logicalZ r * XGen r a = XGen r a * logicalZ r := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero]
  have key : (logicalZ r).operators.symplecticInner
      (XGen r a).operators = hammingRowDot r a a := by
    simp only [NQubitPauliOperator.symplecticInner, logicalZ, XGen,
      NQubitPauliOperator.Z, hammingRowDot, hammingEntry,
      PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle]
    congr 1; ext k; split_ifs <;> simp
  rw [key]; exact hammingRowDot_eq_zero r hr a a

private lemma logicalX_commutes_XGen (a : Fin r) :
    logicalX r * XGen r a = XGen r a * logicalX r := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalX, XGen, NQubitPauliOperator.X]
  split_ifs
  · simp [PauliOperator.mulOp]
  · simp [PauliOperator.mulOp]

private lemma logicalZ_commutes_ZGen (a : Fin r) :
    logicalZ r * ZGen r a = ZGen r a * logicalZ r := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalZ, ZGen, NQubitPauliOperator.Z]
  split_ifs
  · simp [PauliOperator.mulOp]
  · simp [PauliOperator.mulOp]

/-- Logical X commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer (hr : 3 ≤ r) :
    logicalX r ∈ centralizer (stabilizerGroup r hr) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure (logicalX r) (stabilizerGroup r hr)
    (generators r) (stabilizerGroup_toSubgroup_eq r hr)]
  intro s hs
  simp only [generators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range] at hs
  rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (logicalX_commutes_ZGen r hr a).symm
  · exact (logicalX_commutes_XGen r a).symm

/-- Logical Z commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer (hr : 3 ≤ r) :
    logicalZ r ∈ centralizer (stabilizerGroup r hr) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure (logicalZ r) (stabilizerGroup r hr)
    (generators r) (stabilizerGroup_toSubgroup_eq r hr)]
  intro s hs
  simp only [generators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range] at hs
  rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (logicalZ_commutes_ZGen r a).symm
  · exact (logicalZ_commutes_XGen r hr a).symm

end QuantumHamming
end StabilizerGroup

end Quantum

import QEC.Stabilizer.Codes.Small.CSS_4_1_2

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace CSS_4_1_2

/-!
# The LNCY code `[[4, 1, 2]]`: logical operators

The logical basis of `CSS_4_1_2.stabilizerCode` derived from the LNCY codewords
```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2,   |1_L⟩ = (|0011⟩ + |1100⟩)/√2
```
`X̄ = XXII` maps `|0_L⟩ ↔ |1_L⟩`. `Z̄ = ZIZI` has eigenvalue `+1` on `|0_L⟩` and
`−1` on `|1_L⟩` (the parity `(-1)^(q₀ + q₂)` of the basis kets is constant on
each codeword). They anticommute: they meet on qubit 0 only.

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[4, 1]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X: `XXII` (meets `ZZII` on qubits 0, 1 — even, so they commute). -/
def logicalX : NQubitPauliGroupElement 4 := σ[XXII]

/-- Logical Z: `ZIZI` (meets `XXXX` on qubits 0, 2 — even, so they commute). -/
def logicalZ : NQubitPauliGroupElement 4 := σ[ZIZI]

/-! ## Anticommutation -/

/-- `X̄ = XXII` and `Z̄ = ZIZI` anticommute (they meet on qubit 0 only). -/
theorem logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the three generators, a
closed conjunction that `decide` settles. -/

/-- `X̄ = XXII` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄ = ZIZI` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-! ## The code with its logical basis `Code[[4, 1]]ₗ` -/

/-- The single logical qubit `(X̄, Z̄)`. -/
private def logicalOps4_1_2 : Fin 1 → LogicalQubitOps 4 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩

/-- The LNCY code with its logical basis `X̄ = XXII`, `Z̄ = ZIZI`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[4, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps4_1_2
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end CSS_4_1_2
end StabilizerGroup

end Quantum

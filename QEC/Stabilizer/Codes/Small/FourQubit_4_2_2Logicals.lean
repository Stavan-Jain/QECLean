import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace FourQubit_4_2_2

/-!
# The four-qubit code `[[4, 2, 2]]`: logical operators

The logical basis of `FourQubit_4_2_2.stabilizerCode` matching the codeword
basis
```
|0̄0̄⟩ = (|0000⟩ + |1111⟩)/√2
|0̄1̄⟩ = (|0011⟩ + |1100⟩)/√2
|1̄0̄⟩ = (|0101⟩ + |1010⟩)/√2
|1̄1̄⟩ = (|0110⟩ + |1001⟩)/√2
```
namely
```
X̄₁ = IXIX,  X̄₂ = IIXX,  Z̄₁ = IIZZ,  Z̄₂ = IZIZ.
```
Each `X̄ℓ` anticommutes with its own `Z̄ℓ` (one shared qubit) and commutes with
the other logical qubit's operators (two shared qubits, or the same type).

## Outline

- Logical operators `logicalX_1`, `logicalX_2`, `logicalZ_1`, `logicalZ_2`
- (Anti)commutation: `logicalX_ℓ_anticommutes_logicalZ_ℓ` and the four
  off-diagonal commutations
- Centralizer membership `logicalX_ℓ_mem_centralizer`,
  `logicalZ_ℓ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[4, 2]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X for logical qubit 1: `IXIX`. -/
def logicalX_1 : NQubitPauliGroupElement 4 := σ[IXIX]

/-- Logical X for logical qubit 2: `IIXX`. -/
def logicalX_2 : NQubitPauliGroupElement 4 := σ[IIXX]

/-- Logical Z for logical qubit 1: `IIZZ`. -/
def logicalZ_1 : NQubitPauliGroupElement 4 := σ[IIZZ]

/-- Logical Z for logical qubit 2: `IZIZ`. -/
def logicalZ_2 : NQubitPauliGroupElement 4 := σ[IZIZ]

/-! ## (Anti)commutation -/

/-- `X̄₁ = IXIX` and `Z̄₁ = IIZZ` anticommute (they meet on qubit 3 only). -/
theorem logicalX_1_anticommutes_logicalZ_1 : Anticommute logicalX_1 logicalZ_1 := by
  decide

/-- `X̄₂ = IIXX` and `Z̄₂ = IZIZ` anticommute (they meet on qubit 3 only). -/
theorem logicalX_2_anticommutes_logicalZ_2 : Anticommute logicalX_2 logicalZ_2 := by
  decide

/-- `X̄₁` and `X̄₂` commute (both X-type). -/
theorem logicalX_1_commutes_logicalX_2 : logicalX_1 * logicalX_2 = logicalX_2 * logicalX_1 := by
  decide

/-- `X̄₁ = IXIX` and `Z̄₂ = IZIZ` commute (they meet on qubits 1 and 3). -/
theorem logicalX_1_commutes_logicalZ_2 : logicalX_1 * logicalZ_2 = logicalZ_2 * logicalX_1 := by
  decide

/-- `X̄₂ = IIXX` and `Z̄₁ = IIZZ` commute (they meet on qubits 2 and 3). -/
theorem logicalX_2_commutes_logicalZ_1 : logicalX_2 * logicalZ_1 = logicalZ_1 * logicalX_2 := by
  decide

/-- `Z̄₁` and `Z̄₂` commute (both Z-type). -/
theorem logicalZ_1_commutes_logicalZ_2 : logicalZ_1 * logicalZ_2 = logicalZ_2 * logicalZ_1 := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the two generators, a
closed conjunction that `decide` settles. -/

/-- `X̄₁ = IXIX` commutes with every element of the stabilizer. -/
theorem logicalX_1_mem_centralizer : logicalX_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `X̄₂ = IIXX` commutes with every element of the stabilizer. -/
theorem logicalX_2_mem_centralizer : logicalX_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄₁ = IIZZ` commutes with every element of the stabilizer. -/
theorem logicalZ_1_mem_centralizer : logicalZ_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄₂ = IZIZ` commutes with every element of the stabilizer. -/
theorem logicalZ_2_mem_centralizer : logicalZ_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-! ## The code with its logical basis `Code[[4, 2]]ₗ` -/

/-- The two logical qubits `(X̄₁, Z̄₁)`, `(X̄₂, Z̄₂)`. -/
private def logicalOps4_2_2 : Fin 2 → LogicalQubitOps 4 stabilizerGroup
  | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
      logicalX_1_anticommutes_logicalZ_1⟩
  | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
      logicalX_2_anticommutes_logicalZ_2⟩

/-- The `[[4, 2, 2]]` code with its logical basis `(X̄₁, Z̄₁)`, `(X̄₂, Z̄₂)`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[4, 2]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps4_2_2
  logical_commute_cross := by
    intro ℓ ℓ' hne
    fin_cases ℓ <;> fin_cases ℓ'
    · exact (hne rfl).elim
    · exact ⟨logicalX_1_commutes_logicalX_2, logicalX_1_commutes_logicalZ_2,
        logicalX_2_commutes_logicalZ_1.symm, logicalZ_1_commutes_logicalZ_2⟩
    · exact ⟨logicalX_1_commutes_logicalX_2.symm, logicalX_2_commutes_logicalZ_1,
        logicalX_1_commutes_logicalZ_2.symm, logicalZ_1_commutes_logicalZ_2.symm⟩
    · exact (hne rfl).elim

end FourQubit_4_2_2
end StabilizerGroup

end Quantum

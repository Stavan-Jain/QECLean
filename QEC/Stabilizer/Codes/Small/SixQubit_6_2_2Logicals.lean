import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace SixQubit_6_2_2

/-!
# Knill's `C₆` code `[[6, 2, 2]]`: logical operators

The logical basis of `SixQubit_6_2_2.stabilizerCode`, per Knill 2004 (via EC
Zoo `stab_6_2_2`):
```
X̄₁ = IIXXII   (= X_L, weight 2, support {2,3})
Z̄₁ = ZIIZZI   (= Z_L, weight 3, support {0,3,4})
X̄₂ = IXIXXI   (= X_S, weight 3, support {1,3,4})
Z̄₂ = IIIIZZ   (= Z_S, weight 2, support {4,5})
```
Index `1` is Knill's "L" pair (long support on Z, short on X); index `2` is
Knill's "S" pair (short support on Z, mid support on X). `X̄₁` anticommutes with
`Z̄₁` (shared qubit 3) and `X̄₂` with `Z̄₂` (shared qubit 4); every other pair
commutes (an even overlap, or the same type).

## Outline

- Logical operators `logicalX_1`, `logicalX_2`, `logicalZ_1`, `logicalZ_2`
- (Anti)commutation: `logicalX_ℓ_anticommutes_logicalZ_ℓ` and the four
  off-diagonal commutations
- Centralizer membership `logicalX_ℓ_mem_centralizer`,
  `logicalZ_ℓ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[6, 2]]ₗ`
-/

open NQubitPauliGroupElement

/-! ## Logical operators -/

/-- Logical X for logical qubit 1: `IIXXII` (X on qubits 2, 3). -/
def logicalX_1 : NQubitPauliGroupElement 6 := σ[IIXXII]

/-- Logical X for logical qubit 2: `IXIXXI` (X on qubits 1, 3, 4). -/
def logicalX_2 : NQubitPauliGroupElement 6 := σ[IXIXXI]

/-- Logical Z for logical qubit 1: `ZIIZZI` (Z on qubits 0, 3, 4). -/
def logicalZ_1 : NQubitPauliGroupElement 6 := σ[ZIIZZI]

/-- Logical Z for logical qubit 2: `IIIIZZ` (Z on qubits 4, 5). -/
def logicalZ_2 : NQubitPauliGroupElement 6 := σ[IIIIZZ]

/-! ## (Anti)commutation -/

/-- `X̄₁ = IIXXII` and `Z̄₁ = ZIIZZI` anticommute (they meet on qubit 3
only). -/
theorem logicalX_1_anticommutes_logicalZ_1 : Anticommute logicalX_1 logicalZ_1 := by
  decide

/-- `X̄₂ = IXIXXI` and `Z̄₂ = IIIIZZ` anticommute (they meet on qubit 4
only). -/
theorem logicalX_2_anticommutes_logicalZ_2 : Anticommute logicalX_2 logicalZ_2 := by
  decide

/-- `X̄₁` and `X̄₂` commute (both X-type). -/
theorem logicalX_1_commutes_logicalX_2 : logicalX_1 * logicalX_2 = logicalX_2 * logicalX_1 := by
  decide

/-- `X̄₁ = IIXXII` and `Z̄₂ = IIIIZZ` commute (disjoint supports). -/
theorem logicalX_1_commutes_logicalZ_2 : logicalX_1 * logicalZ_2 = logicalZ_2 * logicalX_1 := by
  decide

/-- `X̄₂ = IXIXXI` and `Z̄₁ = ZIIZZI` commute (they meet on qubits 3 and 4). -/
theorem logicalX_2_commutes_logicalZ_1 : logicalX_2 * logicalZ_1 = logicalZ_1 * logicalX_2 := by
  decide

/-- `Z̄₁` and `Z̄₂` commute (both Z-type). -/
theorem logicalZ_1_commutes_logicalZ_2 : logicalZ_1 * logicalZ_2 = logicalZ_2 * logicalZ_1 := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the four generators, a
closed conjunction that `decide` settles. Against a Z-check, an X-type logical
meets it in an even number of qubits (`X̄₁`: `{2,3}` and `∅`; `X̄₂`: `{1,3}` and
`{1,4}`), and dually for the Z-type logicals against the X-checks. -/

/-- `X̄₁ = IIXXII` commutes with every element of the stabilizer. -/
theorem logicalX_1_mem_centralizer : logicalX_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `X̄₂ = IXIXXI` commutes with every element of the stabilizer. -/
theorem logicalX_2_mem_centralizer : logicalX_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄₁ = ZIIZZI` commutes with every element of the stabilizer. -/
theorem logicalZ_1_mem_centralizer : logicalZ_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-- `Z̄₂ = IIIIZZ` commutes with every element of the stabilizer. -/
theorem logicalZ_2_mem_centralizer : logicalZ_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure _ _ _ stabilizerGroup_toSubgroup_eq]
  simp only [generatorsList, listToSet_cons, listToSet_nil, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, forall_eq_or_imp, forall_eq]
  decide

/-! ## The code with its logical basis `Code[[6, 2]]ₗ` -/

/-- The two logical qubits `(X̄₁, Z̄₁)`, `(X̄₂, Z̄₂)`. -/
private def logicalOps6_2_2 : Fin 2 → LogicalQubitOps 6 stabilizerGroup
  | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
      logicalX_1_anticommutes_logicalZ_1⟩
  | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
      logicalX_2_anticommutes_logicalZ_2⟩

/-- The C₆ code with its logical basis `(X̄₁, Z̄₁)`, `(X̄₂, Z̄₂)`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[6, 2]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps := logicalOps6_2_2
  logical_commute_cross := by
    intro ℓ ℓ' hne
    fin_cases ℓ <;> fin_cases ℓ'
    · exact (hne rfl).elim
    · exact ⟨logicalX_1_commutes_logicalX_2, logicalX_1_commutes_logicalZ_2,
        logicalX_2_commutes_logicalZ_1.symm, logicalZ_1_commutes_logicalZ_2⟩
    · exact ⟨logicalX_1_commutes_logicalX_2.symm, logicalX_2_commutes_logicalZ_1,
        logicalX_1_commutes_logicalZ_2.symm, logicalZ_1_commutes_logicalZ_2.symm⟩
    · exact (hne rfl).elim

end SixQubit_6_2_2
end StabilizerGroup

end Quantum

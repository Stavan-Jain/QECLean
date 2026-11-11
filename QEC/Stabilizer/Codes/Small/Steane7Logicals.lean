import QEC.Stabilizer.Codes.Small.Steane7

/-!
# The Steane code `[[7, 1, 3]]`: logical operators

The standard logical basis of `Steane7.stabilizerCode`: transversal `X̄ = X⊗⁷`
and `Z̄ = Z⊗⁷`. Both commute with every check (each row has even weight four)
and they anticommute with each other (seven qubits, an odd number).

## Outline

- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[7, 1]]ₗ`
- CSS type `logicalX_isXType`, `logicalZ_isZType`, and the weight-3
  representative of `X̄`: `minWeightLogical_commutes_logicalX`,
  `minWeightLogical_anticommutes_logicalZ`
- The logical `Y` operator `logicalY = i X̄ Z̄`, with `logicalY_eq_phase2_allY`
-/

namespace Quantum
namespace StabilizerGroup
namespace Steane7

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- Logical X: X on all seven qubits. -/
def logicalX : NQubitPauliGroupElement 7 :=
  ⟨0, NQubitPauliOperator.X 7⟩

/-- Logical Z: Z on all seven qubits. -/
def logicalZ : NQubitPauliGroupElement 7 :=
  ⟨0, NQubitPauliOperator.Z 7⟩

/-! ## Anticommutation -/

/-- `X̄ = X⊗⁷` and `Z̄ = Z⊗⁷` anticommute: they meet on all seven qubits, an odd
number. -/
lemma logicalX_anticommutes_logicalZ : Anticommute logicalX logicalZ := by
  decide

/-! ## Centralizer membership

Commuting with the stabilizer reduces to commuting with the six generators, a
closed statement that `decide` settles. -/

/-- `X̄ = X⊗⁷` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer : logicalX ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-- `Z̄ = Z⊗⁷` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer : logicalZ ∈ centralizer stabilizerGroup :=
  mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq (by decide)

/-! ## The code with its logical basis `Code[[7, 1]]ₗ` -/

/-- The Steane code with its logical basis `X̄ = X⊗⁷`, `Z̄ = Z⊗⁷`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[7, 1]]ₗ where
  toStabilizerCode := stabilizerCode
  logicalOps _ := ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
    logicalX_anticommutes_logicalZ⟩
  logical_commute_cross ℓ ℓ' h := (h (Subsingleton.elim ℓ ℓ')).elim

/-! ## CSS type and the minimum-weight representative

`X̄` is X-type and `Z̄` is Z-type. The weight-3 logical `IIIXIXX` of
`Steane7.lean` is `X̄ · X1`, a representative of `X̄`: it commutes with `X̄` and
anticommutes with `Z̄`. -/

/-- `X̄ = X⊗⁷` is X-type. -/
lemma logicalX_isXType : NQubitPauliOperator.IsXType logicalX.operators := by decide

/-- `Z̄ = Z⊗⁷` is Z-type. -/
lemma logicalZ_isZType : NQubitPauliOperator.IsZType logicalZ.operators := by decide

/-- `IIIXIXX` is X-type. -/
lemma minWeightLogical_isXType : NQubitPauliOperator.IsXType minWeightLogical.operators := by
  decide

/-- `IIIXIXX` commutes with `X̄ = X⊗⁷`. -/
lemma minWeightLogical_commutes_logicalX :
    minWeightLogical * logicalX = logicalX * minWeightLogical := by decide

/-- `IIIXIXX` and `Z̄ = Z⊗⁷` meet on qubits 3, 5 and 6, an odd number. -/
lemma minWeightLogical_anticommutes_logicalZ : Anticommute minWeightLogical logicalZ := by
  decide

/-! ## Logical `Y` -/

/-- Logical Y, with the convention `Ȳ = i X̄ Z̄`. -/
noncomputable def logicalY : NQubitPauliGroupElement 7 :=
  phaseI 7 * (logicalX * logicalZ)

/-- `Ȳ = i X̄ Z̄` is `−Y⊗⁷`: `Y` on all seven qubits with phase power 2. -/
lemma logicalY_eq_phase2_allY : logicalY = ⟨2, NQubitPauliOperator.Y 7⟩ := by
  decide

end Steane7
end StabilizerGroup
end Quantum

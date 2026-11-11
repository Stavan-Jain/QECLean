import QEC.Stabilizer.Codes.Small.Steane7Logicals
import QEC.Stabilizer.Framework.Concatenation

/-!
# The concatenated Steane code `[[49, 1, 9]]`

The concatenation of the Steane code `[[7, 1, 3]]` with itself: each of the
seven qubits of an outer Steane code is encoded into a block of seven qubits
carrying an inner Steane code. The result has `7 · 7 = 49` qubits, one logical
qubit and distance `3 · 3 = 9`.

Its 48 generators are the six Steane checks on each of the seven blocks,
followed by the six Steane checks with `X` replaced by `X⊗⁷` and `Z` by `Z⊗⁷`
on the blocks they act on. The code, its stabilizer group and its logical basis
`X̄ = X⊗⁴⁹`, `Z̄ = Z⊗⁴⁹` come from `Framework/Concatenation`, applied to the
bundle `concatData`.

Nothing here is checked on 49 qubits. The inputs are statements about the
seven-qubit Steane code, all settled by `decide` in `Steane7.lean` and
`Steane7Logicals.lean`:

- its presentation, its logical basis and the CSS types of the checks and the
  logical operators, bundled in `concatData`;
- its distance `3`, used for the inner and for the outer code: every nontrivial
  logical operator of the concatenated code has weight at least `3 · 3`
  (`ConcatCSSData.weight_ge_d1_mul_d2`);
- its weight-3 logical operator `IIIXIXX`, a representative of `X̄ = X⊗⁷`.
  Placing it on blocks 3, 5 and 6 gives a nontrivial logical operator of
  weight `9` (`ConcatCSSData.exists_nontrivial_logical_weight_mul`).

## Outline

- `concatData : ConcatCSSData 7 7 1`
- `stabilizerCode : Code[[49, 1]]`, `stabilizerCodeWithLogicals : Code[[49, 1]]ₗ`
- `code_has_distance_nine`, `stabilizerCodeWithDistance : Code[[49, 1, 9]]`
-/

namespace Quantum
namespace StabilizerGroup
namespace SteaneSteane

open NQubitPauliGroupElement Concatenation Steane7

/-! ## The concatenation data -/

/-- The data for concatenating the Steane code with itself: the Steane code
with its logical basis `X̄ = X⊗⁷`, `Z̄ = Z⊗⁷` as the inner and as the outer code,
and its generators split into the Z-checks `Z1`, `Z2`, `Z3` and the X-checks
`X1`, `X2`, `X3`. -/
noncomputable def concatData : ConcatCSSData 7 7 1 where
  Cin := Steane7.stabilizerCodeWithLogicals
  Cout := Steane7.stabilizerCodeWithLogicals
  Pin := presentation
  Pout := presentation
  Cin_toSubgroup := rfl
  Cout_toSubgroup := rfl
  innerZ := [Z1, Z2, Z3]
  innerX := [X1, X2, X3]
  inner_split := List.Perm.refl _
  innerZ_isZ := zChecks_isZType
  innerX_isX := xChecks_isXType
  outerZ := [Z1, Z2, Z3]
  outerX := [X1, X2, X3]
  outer_split := List.Perm.refl _
  outerZ_isZ := zChecks_isZType
  outerX_isX := xChecks_isXType
  innerLogX_isX := logicalX_isXType
  innerLogX_phaseZero := rfl
  innerLogZ_isZ := logicalZ_isZType
  innerLogZ_phaseZero := rfl
  outerLogX_isX _ := logicalX_isXType
  outerLogZ_isZ _ := logicalZ_isZType

/-! ## The code `Code[[49, 1]]` and its logical basis -/

/-- The concatenated Steane code as a stabilizer code `[[49, 1]]`. -/
noncomputable def stabilizerCode : Code[[49, 1]] := concatData.concatenate

/-- The concatenated Steane code with its logical basis `X̄ = X⊗⁴⁹`,
`Z̄ = Z⊗⁴⁹`: the outer logical operators `X⊗⁷`, `Z⊗⁷` with each factor replaced
by the inner `X⊗⁷`, `Z⊗⁷`. -/
noncomputable def stabilizerCodeWithLogicals : Code[[49, 1]]ₗ :=
  concatData.concatenateWithLogicals

/-! ## Distance 9 -/

/-- **The concatenated Steane code has distance 9.** Both the inner and the
outer code have distance 3, so every nontrivial logical operator has weight at
least `3 · 3`. `IIIXIXX` on each of the blocks 3, 5 and 6 is a nontrivial
logical operator of weight 9: it is the outer logical operator `IIIXIXX` with
each `X` replaced by the inner representative `IIIXIXX` of `X⊗⁷`. -/
theorem code_has_distance_nine : HasCodeDistance stabilizerCode 9 :=
  concatData.concat_hasCodeDistance_of_minWeight
    Steane7.code_has_distance_three Steane7.code_has_distance_three
    minWeightLogical_mem_centralizer minWeightLogical_commutes_logicalX
    minWeightLogical_anticommutes_logicalZ minWeightLogical_weight
    minWeightLogical_mem_centralizer minWeightLogical_isXType
    (ℓ := 0) minWeightLogical_anticommutes_logicalZ minWeightLogical_weight

/-- The concatenated Steane code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[49, 1, 9]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_nine

end SteaneSteane
end StabilizerGroup

end Quantum

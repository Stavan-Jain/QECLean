import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators

/-!
# Logical Clifford actions on one logical qubit

For a logical qubit given by a pair `(X̄, Z̄)` of logical operators
(`LogicalQubitOps`), a logical gate acts as a Clifford gate when it conjugates
`X̄` and `Z̄` like that gate conjugates `X` and `Z`. Conjugation is `U P U†`.

- `LogicalQubitOps.logicalY`, `LogicalQubitOps.logicalNegY`: the derived
  operators `Ȳ = i X̄ Z̄` and `-Ȳ`;
- `LogicalQubitOps.IsLogicalHadamard`: `X̄ ↦ Z̄` and `Z̄ ↦ X̄`;
- `LogicalQubitOps.IsLogicalS`: `Z̄ ↦ Z̄` and `X̄ ↦ Ȳ`;
- `LogicalQubitOps.IsLogicalSAdjoint`: `Z̄ ↦ Z̄` and `X̄ ↦ -Ȳ`.

Each predicate is stated with gate-level conjugation `conjByGate` and has an
equivalent matrix form (`isLogicalHadamard_iff_matrix`, `isLogicalS_iff_matrix`,
`isLogicalSAdjoint_iff_matrix`).
-/

namespace Quantum

variable {n : ℕ}

/-- Conjugating the gate of a Pauli group element `g` by `U` gives the gate of
`h` iff the corresponding matrix identity `U g U† = h` holds. -/
lemma NQubitPauliGroupElement.conjByGate_gate_eq_iff (U : NQubitGate n)
    (g h : NQubitPauliGroupElement n) :
    conjByGate U g.gate = h.gate ↔ U.val * g.toMatrix * star U.val = h.toMatrix := by
  rw [Subtype.ext_iff, conjByGate_val, gate_val, gate_val]

namespace StabilizerGroup

namespace LogicalQubitOps

open NQubitPauliGroupElement (conjByGate_gate_eq_iff)

/-- The logical `Y` operator of a logical pair `(X̄, Z̄)`: `Ȳ = i X̄ Z̄`. -/
noncomputable def logicalY {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.phaseI n * (ops.xOp * ops.zOp)

/-- The operator `-Ȳ = -i X̄ Z̄` of a logical pair `(X̄, Z̄)`. -/
noncomputable def logicalNegY {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.phaseNegI n * (ops.xOp * ops.zOp)

/-!
## Logical Hadamard
-/

/-- A gate acts as a logical Hadamard on the logical pair `(X̄, Z̄)` if it is a
logical gate and conjugates `X̄` to `Z̄` and `Z̄` to `X̄`. -/
def IsLogicalHadamard {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) : Prop :=
  IsLogicalGate U S ∧
    conjByGate U ops.xOp.gate = ops.zOp.gate ∧
    conjByGate U ops.zOp.gate = ops.xOp.gate

/-- Matrix form of `IsLogicalHadamard`. -/
theorem isLogicalHadamard_iff_matrix {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) :
    IsLogicalHadamard ops U ↔
      IsLogicalGate U S ∧
        U.val * ops.xOp.toMatrix * star U.val = ops.zOp.toMatrix ∧
        U.val * ops.zOp.toMatrix * star U.val = ops.xOp.toMatrix := by
  rw [IsLogicalHadamard, conjByGate_gate_eq_iff, conjByGate_gate_eq_iff]

/-- A logical Hadamard is a logical gate. -/
theorem IsLogicalHadamard.isLogicalGate {S : StabilizerGroup n}
    {ops : LogicalQubitOps n S} {U : NQubitGate n} :
    IsLogicalHadamard ops U → IsLogicalGate U S :=
  fun h => h.1

/-!
## Logical phase gate
-/

/-- A gate acts as a logical phase gate `S` on the logical pair `(X̄, Z̄)` if it
is a logical gate, fixes `Z̄`, and conjugates `X̄` to `Ȳ = i X̄ Z̄`. -/
def IsLogicalS {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) : Prop :=
  IsLogicalGate U S ∧
    conjByGate U ops.zOp.gate = ops.zOp.gate ∧
    conjByGate U ops.xOp.gate = (logicalY ops).gate

/-- Matrix form of `IsLogicalS`. -/
theorem isLogicalS_iff_matrix {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) :
    IsLogicalS ops U ↔
      IsLogicalGate U S ∧
        U.val * ops.zOp.toMatrix * star U.val = ops.zOp.toMatrix ∧
        U.val * ops.xOp.toMatrix * star U.val = (logicalY ops).toMatrix := by
  rw [IsLogicalS, conjByGate_gate_eq_iff, conjByGate_gate_eq_iff]

/-- A logical phase gate is a logical gate. -/
theorem IsLogicalS.isLogicalGate {S : StabilizerGroup n}
    {ops : LogicalQubitOps n S} {U : NQubitGate n} :
    IsLogicalS ops U → IsLogicalGate U S :=
  fun h => h.1

/-- A gate acts as the inverse logical phase gate `S†` on the logical pair
`(X̄, Z̄)` if it is a logical gate, fixes `Z̄`, and conjugates `X̄` to
`-Ȳ = -i X̄ Z̄`. -/
def IsLogicalSAdjoint {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) : Prop :=
  IsLogicalGate U S ∧
    conjByGate U ops.zOp.gate = ops.zOp.gate ∧
    conjByGate U ops.xOp.gate = (logicalNegY ops).gate

/-- Matrix form of `IsLogicalSAdjoint`. -/
theorem isLogicalSAdjoint_iff_matrix {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) :
    IsLogicalSAdjoint ops U ↔
      IsLogicalGate U S ∧
        U.val * ops.zOp.toMatrix * star U.val = ops.zOp.toMatrix ∧
        U.val * ops.xOp.toMatrix * star U.val = (logicalNegY ops).toMatrix := by
  rw [IsLogicalSAdjoint, conjByGate_gate_eq_iff, conjByGate_gate_eq_iff]

/-- An inverse logical phase gate is a logical gate. -/
theorem IsLogicalSAdjoint.isLogicalGate {S : StabilizerGroup n}
    {ops : LogicalQubitOps n S} {U : NQubitGate n} :
    IsLogicalSAdjoint ops U → IsLogicalGate U S :=
  fun h => h.1

end LogicalQubitOps

end StabilizerGroup
end Quantum

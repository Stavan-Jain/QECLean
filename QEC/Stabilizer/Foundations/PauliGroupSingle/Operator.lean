import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core

/-!
# Pauli operators: gates, matrices and multiplication

- `PauliOperator.toGate` / `PauliOperator.toMatrix`: the gate and matrix of a
  Pauli operator.
- `PauliOperator.mulOp`: the product of two Pauli operators, as a
  `PauliGroupElement` (an operator together with the phase the product picks
  up).
- `PauliOperator.swapXZ`: the map exchanging `X` and `Z`.
-/

namespace Quantum
open Matrix
open scoped BigOperators

namespace PauliOperator

/-- The quantum gate of a Pauli operator. -/
noncomputable def toGate : PauliOperator → OneQubitGate
  | .I => Quantum.I
  | .X => Quantum.X
  | .Y => Quantum.Y
  | .Z => Quantum.Z

/-- The matrix of a Pauli operator; `toGate_val` identifies it with the matrix
underlying `toGate`. -/
noncomputable def toMatrix : PauliOperator → Matrix QubitBasis QubitBasis ℂ
  | .I => 1
  | .X => Xmat
  | .Y => Ymat
  | .Z => Zmat

/-- The matrix underlying `toGate` is `toMatrix`. -/
@[simp] lemma toGate_val (P : PauliOperator) : (P.toGate).val = P.toMatrix := by
  cases P <;> simp [toGate, toMatrix, Quantum.coe_I, Quantum.coe_X, Quantum.coe_Y,
    Quantum.coe_Z, Imat]

/-- The matrix of a Pauli operator is unitary. -/
lemma toMatrix_mem_unitaryGroup (P : PauliOperator) :
    P.toMatrix ∈ Matrix.unitaryGroup QubitBasis ℂ :=
  P.toGate_val ▸ P.toGate.2

@[simp] lemma toMatrix_I : PauliOperator.I.toMatrix = (1 : Matrix QubitBasis QubitBasis ℂ) := rfl
@[simp] lemma toMatrix_X : PauliOperator.X.toMatrix = Xmat := rfl
@[simp] lemma toMatrix_Y : PauliOperator.Y.toMatrix = Ymat := rfl
@[simp] lemma toMatrix_Z : PauliOperator.Z.toMatrix = Zmat := rfl

@[simp] lemma toGate_I : PauliOperator.I.toGate = (Quantum.I : OneQubitGate) := rfl
@[simp] lemma toGate_X : PauliOperator.X.toGate = (Quantum.X : OneQubitGate) := rfl
@[simp] lemma toGate_Y : PauliOperator.Y.toGate = (Quantum.Y : OneQubitGate) := rfl
@[simp] lemma toGate_Z : PauliOperator.Z.toGate = (Quantum.Z : OneQubitGate) := rfl

/-- The product of two Pauli operators, as an operator together with the phase
the product picks up. -/
noncomputable def mulOp : PauliOperator → PauliOperator → PauliGroupElement
  | .I, q => ⟨0, q⟩
  | p, .I => ⟨0, p⟩
  | .X, .X => ⟨0, .I⟩
  | .Y, .Y => ⟨0, .I⟩
  | .Z, .Z => ⟨0, .I⟩
  | .X, .Y => ⟨1, .Z⟩  -- X * Y = iZ
  | .Y, .X => ⟨3, .Z⟩  -- Y * X = -iZ
  | .Y, .Z => ⟨1, .X⟩  -- Y * Z = iX
  | .Z, .Y => ⟨3, .X⟩  -- Z * Y = -iX
  | .Z, .X => ⟨1, .Y⟩  -- Z * X = iY
  | .X, .Z => ⟨3, .Y⟩  -- X * Z = -iY

@[simp] lemma mulOp_I_I : PauliOperator.I.mulOp PauliOperator.I = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_I_X : PauliOperator.I.mulOp PauliOperator.X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_I_Y : PauliOperator.I.mulOp PauliOperator.Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_I_Z : PauliOperator.I.mulOp PauliOperator.Z = ⟨0, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_X_I : PauliOperator.X.mulOp PauliOperator.I = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_X_X : PauliOperator.X.mulOp PauliOperator.X = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_X_Y : PauliOperator.X.mulOp PauliOperator.Y = ⟨1, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_X_Z : PauliOperator.X.mulOp PauliOperator.Z = ⟨3, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Y_I : PauliOperator.Y.mulOp PauliOperator.I = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Y_X : PauliOperator.Y.mulOp PauliOperator.X = ⟨3, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_Y_Y : PauliOperator.Y.mulOp PauliOperator.Y = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_Y_Z : PauliOperator.Y.mulOp PauliOperator.Z = ⟨1, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_Z_I : PauliOperator.Z.mulOp PauliOperator.I = ⟨0, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_Z_X : PauliOperator.Z.mulOp PauliOperator.X = ⟨1, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Z_Y : PauliOperator.Z.mulOp PauliOperator.Y = ⟨3, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_Z_Z : PauliOperator.Z.mulOp PauliOperator.Z = ⟨0, PauliOperator.I⟩ := rfl

/-- Multiplying by the identity on the right changes nothing. -/
lemma mulOp_I (P : PauliOperator) : P.mulOp .I = ⟨0, P⟩ := by cases P <;> rfl

/-- Multiplying by the identity on the left changes nothing. -/
lemma I_mulOp (P : PauliOperator) : PauliOperator.I.mulOp P = ⟨0, P⟩ := by cases P <;> rfl

/-- Every Pauli operator squares to the identity. -/
lemma mulOp_self (P : PauliOperator) : P.mulOp P = ⟨0, .I⟩ := by cases P <;> rfl

/-- The operator part of `mulOp` is commutative; only the phase depends on the
order. -/
lemma mulOp_operator_comm (P Q : PauliOperator) :
    (P.mulOp Q).operator = (Q.mulOp P).operator := by
  cases P <;> cases Q <;> rfl

/-- The operator part of `mulOp` is associative. -/
lemma mulOp_operator_assoc (P Q R : PauliOperator) :
    ((P.mulOp Q).operator.mulOp R).operator = (P.mulOp (Q.mulOp R).operator).operator := by
  cases P <;> cases Q <;> cases R <;> rfl

/-- The phase part of associativity of `mulOp`: both bracketings of a triple
product pick up the same total phase. -/
lemma mulOp_phasePower_assoc (P Q R : PauliOperator) :
    (P.mulOp Q).phasePower + ((P.mulOp Q).operator.mulOp R).phasePower =
      (Q.mulOp R).phasePower + (P.mulOp (Q.mulOp R).operator).phasePower := by
  cases P <;> cases Q <;> cases R <;> rfl

/-- Two Pauli operators commute exactly when they are equal or one of them is
the identity. -/
lemma mulOp_comm_iff (P Q : PauliOperator) :
    P.mulOp Q = Q.mulOp P ↔ (P = Q ∨ P = PauliOperator.I ∨ Q = PauliOperator.I) := by
  cases P <;> cases Q <;> simp

/-- Two Pauli operators either commute (equal phases in either order) or
anticommute (the phases differ by `2`, a factor of `-1`). -/
lemma mulOp_phasePower_eq_or_eq_add_two (P Q : PauliOperator) :
    (P.mulOp Q).phasePower = (Q.mulOp P).phasePower ∨
      (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 := by
  cases P <;> cases Q <;> decide

/-- Exchange `X` and `Z`, fixing `I` and `Y`: the action of conjugation by the
Hadamard gate, up to sign. -/
def swapXZ : PauliOperator → PauliOperator
  | .X => .Z
  | .Z => .X
  | p => p

end PauliOperator

end Quantum

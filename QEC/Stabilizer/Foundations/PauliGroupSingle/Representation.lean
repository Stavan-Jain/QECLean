import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Star.Basic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator
import QEC.Stabilizer.Foundations.PauliGroupSingle.Phase
import QEC.Stabilizer.Foundations.PauliGroupSingle.Element

/-!
# Matrix and gate representation of the single-qubit Pauli group

`PauliGroupElement.toGate` and `PauliGroupElement.toMatrix` send `i ^ k * P` to
the corresponding scaled gate and matrix. Both are multiplicative
(`toGate_mul`, `toMatrix_mul`) and preserve inverses (`toGate_inv`,
`toMatrix_inv`).
-/

namespace Quantum
open Matrix
open scoped BigOperators

/-- The matrix product of two Pauli matrices is the matrix of their `mulOp`,
scaled by the phase it carries. -/
lemma PauliOperator.toMatrix_mul (P Q : PauliOperator) :
    P.toMatrix * Q.toMatrix =
      PauliGroupElement.phasePowerToComplex (P.mulOp Q).phasePower •
        (P.mulOp Q).operator.toMatrix := by
  cases P <;> cases Q <;>
    simp [Xmat_mul_Ymat, Xmat_mul_Zmat, Ymat_mul_Xmat, Ymat_mul_Zmat, Zmat_mul_Xmat,
      Zmat_mul_Ymat]

namespace PauliGroupElement

/-- The quantum gate of a Pauli group element: the operator's gate scaled by
the phase. -/
noncomputable def toGate (p : PauliGroupElement) : OneQubitGate :=
  phasePowerToUnitComplex p.phasePower • (PauliOperator.toGate p.operator)

/-- The matrix of a Pauli group element, as the matrix underlying `toGate`. -/
@[simp] noncomputable def toMatrix (p : PauliGroupElement) : Matrix QubitBasis QubitBasis ℂ :=
  (toGate p).val

/-- The matrix underlying `toGate` is `toMatrix`. -/
lemma toGate_val (p : PauliGroupElement) : (toGate p).val = toMatrix p := rfl

@[simp] lemma toMatrix_one : toMatrix (1 : PauliGroupElement) = 1 := by
  simp [toMatrix, toGate, one_def, PauliOperator.toGate, phasePowerToComplex_0, Quantum.coe_I,
    Imat]

/-- The matrix of a Pauli group element is unitary. -/
lemma toMatrix_mem_unitaryGroup (p : PauliGroupElement) :
    toMatrix p ∈ Matrix.unitaryGroup QubitBasis ℂ :=
  (toGate p).property

@[simp] lemma toGate_one : toGate (1 : PauliGroupElement) = (1 : OneQubitGate) :=
  Subtype.ext toMatrix_one

/-- `toMatrix` is multiplicative. -/
lemma toMatrix_mul (p q : PauliGroupElement) :
    toMatrix (p * q) = toMatrix p * toMatrix q := by
  simp only [toMatrix, toGate, smul_UnitComplex_gate_val, PauliOperator.toGate_val,
    phasePowerToUnitComplex_coe, mul_eq, mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    PauliOperator.toMatrix_mul, ← phasePowerToComplex_add]
  congr 1
  ring

/-- `toGate` is multiplicative. -/
lemma toGate_mul (p q : PauliGroupElement) : toGate (p * q) = toGate p * toGate q :=
  Subtype.ext (toMatrix_mul p q)

/-- `toGate` preserves inverses. -/
lemma toGate_inv (p : PauliGroupElement) : toGate (p⁻¹) = (toGate p)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← toGate_mul, inv_mul_cancel, toGate_one])

/-- `toMatrix` preserves inverses. -/
lemma toMatrix_inv (p : PauliGroupElement) : toMatrix (p⁻¹) = (toMatrix p)⁻¹ := by
  simp only [toMatrix]
  rw [toGate_inv, gate_inv_val, gate_val_inv]

end PauliGroupElement

end Quantum

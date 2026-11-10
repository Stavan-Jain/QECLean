import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Matrix and gate representation of the n-qubit Pauli group

`NQubitPauliGroupElement.toMatrix` and `NQubitPauliGroupElement.toGate` are
faithful representations of the n-qubit Pauli group:

- they are multiplicative (`toMatrix_mul`, `toGate_mul`) and preserve inverses
  (`toMatrix_inv`, `toGate_inv`);
- they are injective (`toMatrix_inj`, `toGate_inj`), which follows from the
  trace orthogonality of Pauli matrices (`NQubitPauliOperator.trace_mul`).
-/

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-!
## Products and traces of Pauli operator matrices
-/

/-- The trace of a product of two Pauli matrices is `2` if they are equal and
`0` otherwise. -/
lemma PauliOperator.trace_mul (p q : PauliOperator) :
    (p.toMatrix * q.toMatrix).trace = if p = q then 2 else 0 := by
  cases p <;> cases q <;> simp +decide [Matrix.trace, Xmat, Ymat, Zmat] <;> norm_num

/-- The matrix of `mulOp p q` is the product of the matrices of `p` and `q`:
`mulOp` records exactly the phase that the matrix product picks up. -/
lemma NQubitPauliGroupElement.toMatrix_mulOp (p q : NQubitPauliOperator n) :
    (NQubitPauliGroupElement.mulOp p q).toMatrix = p.toMatrix * q.toMatrix := by
  simp only [NQubitPauliOperator.toMatrix_eq_tensorMatrix, tensorMatrix_mul,
    PauliOperator.toMatrix_mul, tensorMatrix_smul, NQubitPauliGroupElement.toMatrix,
    NQubitPauliGroupElement.mulOp, PauliGroupElement.phasePowerToComplex_sum]

namespace NQubitPauliOperator

/-- The trace of a product of two n-qubit Pauli matrices is the product of the
traces of the single-qubit products. -/
lemma trace_matrix_mul (p q : NQubitPauliOperator n) :
    (p.toMatrix * q.toMatrix).trace = ∏ i, ((p i).toMatrix * (q i).toMatrix).trace := by
  rw [toMatrix_eq_tensorMatrix, toMatrix_eq_tensorMatrix, tensorMatrix_mul, trace_tensorMatrix]

/-- Trace orthogonality: the trace of a product of two n-qubit Pauli matrices is
`2 ^ n` if the operators are equal and `0` otherwise. -/
lemma trace_mul (p q : NQubitPauliOperator n) :
    (p.toMatrix * q.toMatrix).trace = if p = q then (2 : ℂ) ^ n else 0 := by
  rw [trace_matrix_mul]
  split_ifs with h
  · subst h
    simp [PauliOperator.trace_mul]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [PauliOperator.trace_mul, hi])

end NQubitPauliOperator

namespace NQubitPauliGroupElement

/-!
## The representation is multiplicative
-/

@[simp] lemma toMatrix_one (n : ℕ) :
    (1 : NQubitPauliGroupElement n).toMatrix = (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  simp [toMatrix, NQubitPauliOperator.identity_toMatrix]

/-- The matrix of `minusOne n` is `-1` times the identity matrix. -/
@[simp] lemma minusOne_toMatrix (n : ℕ) :
    (minusOne n).toMatrix = (-1 : ℂ) • (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  rw [toMatrix, minusOne_operators, minusOne_phasePower, PauliGroupElement.phasePowerToComplex_2,
    NQubitPauliOperator.identity_toMatrix]

@[simp] lemma toGate_one (n : ℕ) :
    toGate (1 : NQubitPauliGroupElement n) = (1 : QuantumGate (NQubitBasis n)) := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_one]
  rfl

/-- `toMatrix` is multiplicative. -/
lemma toMatrix_mul (p q : NQubitPauliGroupElement n) :
    (p * q).toMatrix = p.toMatrix * q.toMatrix := by
  simp only [toMatrix, mul_eq, mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← toMatrix_mulOp, ← PauliGroupElement.phasePowerToComplex_add]
  congr 1
  ring

/-- `toMatrix` preserves inverses. -/
lemma toMatrix_inv (p : NQubitPauliGroupElement n) : (p⁻¹).toMatrix = (p.toMatrix)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← toMatrix_mul, mul_inv_cancel, toMatrix_one])).symm

/-- `toGate` is multiplicative. -/
lemma toGate_mul (p q : NQubitPauliGroupElement n) : toGate (p * q) = toGate p * toGate q := by
  apply Subtype.ext
  rw [toGate_val, gate_mul_val, toGate_val, toGate_val]
  exact toMatrix_mul p q

/-- `toGate` preserves inverses. -/
lemma toGate_inv (p : NQubitPauliGroupElement n) : toGate (p⁻¹) = (toGate p)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← toGate_mul, inv_mul_cancel, toGate_one])

/-- Two elements have the same matrix iff they have the same gate. -/
lemma toMatrix_eq_iff_toGate_eq (p q : NQubitPauliGroupElement n) :
    toMatrix p = toMatrix q ↔ toGate p = toGate q := by
  rw [Subtype.ext_iff, toGate_val, toGate_val]

/-!
## The representation is faithful
-/

/-- `toMatrix` is injective: the matrix of a Pauli group element determines both
its operator part and its phase. -/
lemma toMatrix_inj (p q : NQubitPauliGroupElement n) (h : toMatrix p = toMatrix q) : p = q := by
  have h_trace :
      PauliGroupElement.phasePowerToComplex p.phasePower *
          (p.operators.toMatrix * p.operators.toMatrix).trace =
        PauliGroupElement.phasePowerToComplex q.phasePower *
          (q.operators.toMatrix * p.operators.toMatrix).trace := by
    simpa [toMatrix] using congrArg (fun M => (M * p.operators.toMatrix).trace) h
  rw [NQubitPauliOperator.trace_mul, NQubitPauliOperator.trace_mul, if_pos rfl] at h_trace
  have h_ops : q.operators = p.operators := by
    by_contra hne
    simp [hne, PauliGroupElement.phasePowerToComplex_ne_zero] at h_trace
  refine NQubitPauliGroupElement.ext _ _ (PauliGroupElement.phasePowerToComplex_injective ?_)
    h_ops.symm
  simpa [h_ops] using h_trace

/-- `toGate` is injective. -/
lemma toGate_inj (p q : NQubitPauliGroupElement n) (h : toGate p = toGate q) : p = q :=
  toMatrix_inj p q ((toMatrix_eq_iff_toGate_eq p q).mpr h)

end NQubitPauliGroupElement

end Quantum

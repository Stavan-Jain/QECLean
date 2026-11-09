import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator

/-!
# The n-qubit Pauli group

An element of the n-qubit Pauli group is an n-qubit Pauli operator together with
a global phase `i ^ k`. This file defines the type `NQubitPauliGroupElement n`,
its matrix and gate, the group structure, and the `support` and `weight` of an
element.
-/

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- An element `i ^ k * (P₀ ⊗ P₁ ⊗ ... ⊗ Pₙ₋₁)` of the n-qubit Pauli group:
a global phase power `phasePower : Fin 4` and an n-qubit Pauli operator
`operators`. -/
structure NQubitPauliGroupElement (n : ℕ) where
  phasePower : Fin 4  -- 0 → 1, 1 → i, 2 → -1, 3 → -i
  operators : NQubitPauliOperator n

/-- Two n-qubit Pauli group elements are equal when their phases and operators
are. -/
@[ext] theorem NQubitPauliGroupElement.ext {n : ℕ} (p q : NQubitPauliGroupElement n)
    (h_phase : p.phasePower = q.phasePower) (h_ops : p.operators = q.operators) : p = q := by
  cases p; cases q; congr

namespace NQubitPauliGroupElement

/-- The matrix of an n-qubit Pauli group element: the matrix of its operator,
scaled by its phase. -/
noncomputable def toMatrix (p : NQubitPauliGroupElement n) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  PauliGroupElement.phasePowerToComplex p.phasePower • p.operators.toMatrix

/-- The quantum gate of an n-qubit Pauli group element: the gate of its
operator, scaled by its phase. -/
noncomputable def toGate (p : NQubitPauliGroupElement n) : QuantumGate (NQubitBasis n) :=
  PauliGroupElement.phasePowerToUnitComplex p.phasePower • (p.operators.toGate)

/-- Alias of `toGate`, for statements phrased in terms of gates. -/
noncomputable abbrev gate (p : NQubitPauliGroupElement n) : QuantumGate (NQubitBasis n) :=
  toGate p

@[simp] lemma gate_eq_toGate (p : NQubitPauliGroupElement n) : p.gate = p.toGate := rfl

/-- The matrix underlying `toGate` is `toMatrix`. -/
lemma toGate_val (p : NQubitPauliGroupElement n) : (toGate p).val = toMatrix p := by
  simp [toMatrix, toGate, smul_UnitComplex_gate_val, NQubitPauliOperator.toGate_val,
    PauliGroupElement.phasePowerToUnitComplex_coe]

/-- The matrix underlying `gate` is `toMatrix`. -/
@[simp] lemma gate_val (p : NQubitPauliGroupElement n) : p.gate.val = p.toMatrix :=
  toGate_val p

/-- The identity element of the n-qubit Pauli group: `I ⊗ I ⊗ ... ⊗ I` with
phase `1`. -/
def one (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.identity n⟩

/-- The central element `-1` of the n-qubit Pauli group. -/
def minusOne (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨2, NQubitPauliOperator.identity n⟩

/-- The central element `i` of the n-qubit Pauli group. -/
def phaseI (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨1, NQubitPauliOperator.identity n⟩

/-- The central element `-i` of the n-qubit Pauli group. -/
def phaseNegI (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨3, NQubitPauliOperator.identity n⟩

/-- The n-qubit Pauli group element with the given operator and phase `1`. -/
def ofOperator (op : NQubitPauliOperator n) : NQubitPauliGroupElement n :=
  ⟨0, op⟩

@[simp] lemma ofOperator_phasePower (op : NQubitPauliOperator n) :
    (ofOperator op).phasePower = 0 := rfl

@[simp] lemma ofOperator_operators (op : NQubitPauliOperator n) :
    (ofOperator op).operators = op := rfl

@[simp] lemma one_phasePower (n : ℕ) : (one n).phasePower = 0 := rfl
@[simp] lemma one_operators (n : ℕ) : (one n).operators = NQubitPauliOperator.identity n := rfl

@[simp] lemma minusOne_phasePower (n : ℕ) : (minusOne n).phasePower = 2 := rfl
@[simp] lemma minusOne_operators (n : ℕ) :
    (minusOne n).operators = NQubitPauliOperator.identity n := rfl

@[simp] lemma phaseI_phasePower (n : ℕ) : (phaseI n).phasePower = 1 := rfl
@[simp] lemma phaseI_operators (n : ℕ) :
    (phaseI n).operators = NQubitPauliOperator.identity n := rfl

@[simp] lemma phaseNegI_phasePower (n : ℕ) : (phaseNegI n).phasePower = 3 := rfl
@[simp] lemma phaseNegI_operators (n : ℕ) :
    (phaseNegI n).operators = NQubitPauliOperator.identity n := rfl

/-- The product of two n-qubit Pauli operators, computed qubit by qubit: the
operator part is the qubitwise product, and the phase is the sum of the phases
the single-qubit products pick up. -/
noncomputable def mulOp (p q : NQubitPauliOperator n) : NQubitPauliGroupElement n :=
  ⟨∑ i, ((p i).mulOp (q i)).phasePower, fun i => ((p i).mulOp (q i)).operator⟩

/-- `p *ₚ q` is `mulOp p q`, the product of two n-qubit Pauli operators. -/
infixl:70 " *ₚ " => mulOp

/-- Multiplication in the n-qubit Pauli group: the phases add, together with
the phase contributed by the product of the operators. -/
noncomputable def mul (p q : NQubitPauliGroupElement n) : NQubitPauliGroupElement n :=
  ⟨p.phasePower + q.phasePower + (mulOp p.operators q.operators).phasePower,
  (mulOp p.operators q.operators).operators⟩

/-- Inversion in the n-qubit Pauli group: Pauli operators are involutions, so
only the phase is negated. -/
noncomputable def inv (p : NQubitPauliGroupElement n) : NQubitPauliGroupElement n :=
  ⟨-p.phasePower, p.operators⟩

noncomputable instance : Mul (NQubitPauliGroupElement n) := ⟨mul⟩

@[simp] lemma mul_eq (p q : NQubitPauliGroupElement n) : p * q = mul p q := rfl

noncomputable instance : Inv (NQubitPauliGroupElement n) := ⟨inv⟩

@[simp] lemma inv_eq (p : NQubitPauliGroupElement n) : p⁻¹ = inv p := rfl

/-- The central element `-1` is its own inverse. -/
@[simp] lemma minusOne_inv (n : ℕ) : (minusOne n)⁻¹ = minusOne n :=
  NQubitPauliGroupElement.ext _ _ rfl rfl

noncomputable instance : One (NQubitPauliGroupElement n) := ⟨one n⟩

@[simp] lemma one_def : (1 : NQubitPauliGroupElement n) = ⟨0, NQubitPauliOperator.identity n⟩ := rfl
@[simp] lemma one_phasePower_def (n : ℕ) : (1 : NQubitPauliGroupElement n).phasePower = 0 := rfl
@[simp] lemma one_operators_def (n : ℕ) :
    (1 : NQubitPauliGroupElement n).operators = NQubitPauliOperator.identity n := rfl

/-- Multiplying by the identity operator on the right contributes no phase. -/
lemma mulOp_identity_right_phase (op : NQubitPauliOperator n) :
    (mulOp op (NQubitPauliOperator.identity n)).phasePower = 0 := by
  simp [mulOp, NQubitPauliOperator.identity, PauliOperator.mulOp_I]

/-- Multiplying by the identity operator on the left contributes no phase. -/
lemma mulOp_identity_left_phase (op : NQubitPauliOperator n) :
    (mulOp (NQubitPauliOperator.identity n) op).phasePower = 0 := by
  simp [mulOp, NQubitPauliOperator.identity, PauliOperator.I_mulOp]

/-- Multiplying by the identity operator on the right leaves the operator
unchanged. -/
lemma mulOp_identity_right_op (op : NQubitPauliOperator n) :
    (mulOp op (NQubitPauliOperator.identity n)).operators = op := by
  ext i
  simp [mulOp, NQubitPauliOperator.identity, PauliOperator.mulOp_I]

/-- Multiplying by the identity operator on the left leaves the operator
unchanged. -/
lemma mulOp_identity_left_op (op : NQubitPauliOperator n) :
    (mulOp (NQubitPauliOperator.identity n) op).operators = op := by
  ext i
  simp [mulOp, NQubitPauliOperator.identity, PauliOperator.I_mulOp]

/-- Every n-qubit Pauli operator squares to the identity, with no phase. -/
lemma mulOp_self (op : NQubitPauliOperator n) : mulOp op op = 1 := by
  simp only [mulOp, PauliOperator.mulOp_self, Finset.sum_const_zero]
  rfl

/-- The operator part of `mulOp` is associative. -/
lemma mulOp_operators_assoc (p q r : NQubitPauliOperator n) :
    (mulOp (mulOp p q).operators r).operators = (mulOp p (mulOp q r).operators).operators := by
  ext i
  exact PauliOperator.mulOp_operator_assoc _ _ _

/-- The phase part of associativity of `mulOp`: both bracketings of a triple
product pick up the same total phase. -/
lemma mulOp_phasePower_assoc (p q r : NQubitPauliOperator n) :
    (mulOp p q).phasePower + (mulOp (mulOp p q).operators r).phasePower =
      (mulOp q r).phasePower + (mulOp p (mulOp q r).operators).phasePower := by
  simp only [mulOp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => PauliOperator.mulOp_phasePower_assoc _ _ _

@[simp] lemma mul_one (p : NQubitPauliGroupElement n) : p * 1 = p := by
  ext i <;> simp [mul, mulOp_identity_right_phase, mulOp_identity_right_op]

@[simp] lemma one_mul (p : NQubitPauliGroupElement n) : 1 * p = p := by
  ext i <;> simp [mul, mulOp_identity_left_phase, mulOp_identity_left_op]

/-- Inversion changes only the phase, not the operator part. -/
@[simp] lemma inv_operators (p : NQubitPauliGroupElement n) : (p⁻¹).operators = p.operators :=
  rfl

/-- If `p` and `q` have the same operator part, then `p * q⁻¹` is a pure phase:
its operator part is the identity. -/
lemma mul_inv_operators_identity_of_eq_operators (p q : NQubitPauliGroupElement n)
    (h : p.operators = q.operators) :
    (p * q⁻¹).operators = NQubitPauliOperator.identity n := by
  rw [mul_eq, mul, inv_operators, h, mulOp_self]
  rfl

@[simp] lemma mul_right_inv (p : NQubitPauliGroupElement n) : p * p⁻¹ = 1 := by
  simp [mul, inv, mulOp_self]

@[simp] lemma mul_left_inv (p : NQubitPauliGroupElement n) : p⁻¹ * p = 1 := by
  simp [mul, inv, mulOp_self]

open Fin.CommRing in
/-- Multiplication in the n-qubit Pauli group is associative. -/
theorem mul_assoc (p q r : NQubitPauliGroupElement n) : (p * q) * r = p * (q * r) := by
  refine NQubitPauliGroupElement.ext _ _ ?_ (mulOp_operators_assoc _ _ _)
  simp only [mul_eq, mul]
  linear_combination mulOp_phasePower_assoc p.operators q.operators r.operators

/-- The n-qubit Pauli group is a group under multiplication. -/
noncomputable instance : Group (NQubitPauliGroupElement n) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := mul_left_inv

/-!
## Pauli weight and support

The **support** and **weight** of a group element are those of its operator
part; the phase does not affect them.
-/

/-- The support of an n-qubit Pauli group element: the qubits where its
operator is not `I`. -/
def support (p : NQubitPauliGroupElement n) : Finset (Fin n) :=
  NQubitPauliOperator.support p.operators

/-- The Pauli weight: the number of qubits on which the element acts
nontrivially. -/
def weight (p : NQubitPauliGroupElement n) : ℕ :=
  NQubitPauliOperator.weight p.operators

@[simp] lemma support_ofOperator (op : NQubitPauliOperator n) :
    support (ofOperator op) = NQubitPauliOperator.support op := rfl

@[simp] lemma weight_ofOperator (op : NQubitPauliOperator n) :
    weight (ofOperator op) = NQubitPauliOperator.weight op := rfl

@[simp] lemma support_one (n : ℕ) : support (1 : NQubitPauliGroupElement n) = ∅ := by
  simp [support, one_def, NQubitPauliOperator.support_identity]

@[simp] lemma weight_one (n : ℕ) : weight (1 : NQubitPauliGroupElement n) = 0 := by
  simp [weight, one_def, NQubitPauliOperator.weight_identity]

lemma mem_support (p : NQubitPauliGroupElement n) (i : Fin n) :
    i ∈ support p ↔ p.operators i ≠ PauliOperator.I :=
  NQubitPauliOperator.mem_support p.operators i

/-- An element has weight zero iff its operator part is the identity. -/
lemma weight_eq_zero_iff (p : NQubitPauliGroupElement n) :
    weight p = 0 ↔ p.operators = NQubitPauliOperator.identity n :=
  NQubitPauliOperator.weight_eq_zero_iff p.operators

end NQubitPauliGroupElement

end Quantum

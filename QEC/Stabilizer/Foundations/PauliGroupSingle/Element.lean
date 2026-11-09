import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator

/-!
# The single-qubit Pauli group

The group structure on `PauliGroupElement`: phases add, and operators multiply
through `PauliOperator.mulOp`, which contributes its own phase.
-/

namespace Quantum

namespace PauliGroupElement

/-- The identity element of the Pauli group: `I` with phase `1`. -/
def one : PauliGroupElement := ⟨0, PauliOperator.I⟩

/-- The Pauli operator `X` with phase `1`. -/
def X : PauliGroupElement := ⟨0, PauliOperator.X⟩

/-- The Pauli operator `Y` with phase `1`. -/
def Y : PauliGroupElement := ⟨0, PauliOperator.Y⟩

/-- The Pauli operator `Z` with phase `1`. -/
def Z : PauliGroupElement := ⟨0, PauliOperator.Z⟩

/-- Multiplication in the Pauli group. -/
noncomputable def mul (p q : PauliGroupElement) : PauliGroupElement :=
  ⟨p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower,
   (p.operator.mulOp q.operator).operator⟩

/-- Inversion in the Pauli group: Pauli operators are involutions, so only the
phase is negated. -/
noncomputable def inv (p : PauliGroupElement) : PauliGroupElement :=
  ⟨-p.phasePower, p.operator⟩

noncomputable instance : Mul PauliGroupElement := ⟨mul⟩
noncomputable instance : Inv PauliGroupElement := ⟨inv⟩
instance : One PauliGroupElement := ⟨one⟩

@[simp] lemma mul_eq (p q : PauliGroupElement) : p * q = mul p q := rfl
@[simp] lemma inv_eq (p : PauliGroupElement) : p⁻¹ = inv p := rfl
@[simp] lemma inv_operator (p : PauliGroupElement) : (p⁻¹).operator = p.operator := rfl
@[simp] lemma one_def : (1 : PauliGroupElement) = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma X_def : X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma Y_def : Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma Z_def : Z = ⟨0, PauliOperator.Z⟩ := rfl

@[simp] lemma mul_one (p : PauliGroupElement) : p * 1 = p := by
  simp [mul, PauliOperator.mulOp_I]

@[simp] lemma one_mul (p : PauliGroupElement) : 1 * p = p := by
  simp [mul, PauliOperator.I_mulOp]

@[simp] lemma mul_right_inv (p : PauliGroupElement) : p * p⁻¹ = 1 := by
  simp [mul, inv, PauliOperator.mulOp_self]

@[simp] lemma mul_left_inv (p : PauliGroupElement) : p⁻¹ * p = 1 := by
  simp [mul, inv, PauliOperator.mulOp_self]

open Fin.CommRing in
/-- Multiplication in the Pauli group is associative. -/
theorem mul_assoc (p q r : PauliGroupElement) : (p * q) * r = p * (q * r) := by
  refine PauliGroupElement.ext _ _ ?_ ?_
  · simp only [mul_eq, mul]
    linear_combination PauliOperator.mulOp_phasePower_assoc p.operator q.operator r.operator
  · exact PauliOperator.mulOp_operator_assoc _ _ _

/-- The Pauli group is a group under multiplication. -/
noncomputable instance : Group PauliGroupElement where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := mul_left_inv

end PauliGroupElement

end Quantum

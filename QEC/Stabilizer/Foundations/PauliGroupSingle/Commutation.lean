import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator
import QEC.Stabilizer.Foundations.PauliGroupSingle.Element

/-!
# Commutation in the single-qubit Pauli group

The operator part of a product does not depend on the order of the factors, so
whether two Pauli group elements commute is decided by the phase that
`PauliOperator.mulOp` contributes (`commutes_iff_mulOp_phasePower`). Any two
elements commute or anticommute (`commute_or_anticommute`).
-/

namespace Quantum

namespace PauliGroupElement

/-- The operator part of a product is independent of the order of the factors;
only the phase can differ. -/
lemma operator_mul_comm (p q : PauliGroupElement) :
    (p * q).operator = (q * p).operator :=
  PauliOperator.mulOp_operator_comm _ _

/-- Two Pauli group elements commute iff their operators contribute the same
phase when multiplied in either order. -/
lemma commutes_iff_mulOp_phasePower (p q : PauliGroupElement) :
    p * q = q * p ↔
      (p.operator.mulOp q.operator).phasePower = (q.operator.mulOp p.operator).phasePower := by
  constructor
  · intro h
    simpa [mul, add_comm q.phasePower] using congrArg phasePower h
  · intro h
    refine PauliGroupElement.ext _ _ ?_ (operator_mul_comm p q)
    simp [mul, h, add_comm q.phasePower]

/-- Two Pauli group elements commute iff their operators do. -/
lemma commutes_iff (p q : PauliGroupElement) :
    p * q = q * p ↔ p.operator.mulOp q.operator = q.operator.mulOp p.operator := by
  rw [commutes_iff_mulOp_phasePower, PauliGroupElement.ext_iff,
    and_iff_left (PauliOperator.mulOp_operator_comm _ _)]

/-- The central element `-1` of the Pauli group, represented as `i ^ 2 * I`. -/
def minusOne : PauliGroupElement := ⟨2, PauliOperator.I⟩

/-- Any two Pauli group elements commute or anticommute, where anticommuting
means `p * q = minusOne * (q * p)`. -/
lemma commute_or_anticommute (p q : PauliGroupElement) :
    p * q = q * p ∨ p * q = minusOne * (q * p) := by
  rcases PauliOperator.mulOp_phasePower_eq_or_eq_add_two p.operator q.operator with h | h
  · exact Or.inl ((commutes_iff_mulOp_phasePower p q).2 h)
  · refine Or.inr (PauliGroupElement.ext _ _ ?_ ?_)
    · simp only [mul_eq, mul, minusOne, PauliOperator.I_mulOp, h]
      abel
    · simpa [mul, minusOne, PauliOperator.I_mulOp] using operator_mul_comm p q

end PauliGroupElement

end Quantum

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic

/-!
# Single-qubit Pauli group: core types

- `PauliOperator`: the four Pauli operators `I`, `X`, `Y`, `Z`.
- `PauliGroupElement`: a Pauli operator together with a phase `i ^ k`,
  `k : Fin 4`.
-/

namespace Quantum

/-- The four Pauli operators: identity, `X`, `Y` and `Z`. -/
inductive PauliOperator : Type
  | I : PauliOperator
  | X : PauliOperator
  | Y : PauliOperator
  | Z : PauliOperator
deriving DecidableEq

/-- An element `i ^ k * P` of the single-qubit Pauli group, with phase power
`k : Fin 4` and `P : PauliOperator`. -/
structure PauliGroupElement where
  phasePower : Fin 4
  operator : PauliOperator
deriving DecidableEq

/-- Two Pauli group elements are equal when their phases and operators are. -/
@[ext] theorem PauliGroupElement.ext (p q : PauliGroupElement)
    (h_phase : p.phasePower = q.phasePower) (h_op : p.operator = q.operator) : p = q := by
  cases p; cases q; congr

end Quantum

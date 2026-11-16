module

public import QEC.Stabilizer.Foundations.PauliGroupSingle.Core
public import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator
public import QEC.Stabilizer.Foundations.PauliGroupSingle.Phase
public import QEC.Stabilizer.Foundations.PauliGroupSingle.Element
public import QEC.Stabilizer.Foundations.PauliGroupSingle.Representation
public import QEC.Stabilizer.Foundations.PauliGroupSingle.Commutation

/-!
# The single-qubit Pauli group

- `Core`: the types `PauliOperator` and `PauliGroupElement`.
- `Operator`: gates, matrices and multiplication of Pauli operators.
- `Phase`: phase powers as complex numbers.
- `Element`: the group structure on `PauliGroupElement`.
- `Representation`: the matrix and gate of a group element.
- `Commutation`: commutation and anticommutation.
-/

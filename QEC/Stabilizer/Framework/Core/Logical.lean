module

public import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
public import QEC.Stabilizer.Framework.Core.Logical.LogicalOperatorCoset
public import QEC.Stabilizer.Framework.Core.Logical.LogicalGates
public import QEC.Stabilizer.Framework.Core.Logical.LogicalGateGroup
public import QEC.Stabilizer.Framework.Core.Logical.LogicalCliffordAction
public import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Core: logical operators and code distance

- `LogicalOperators`: Pauli logical operators as the centralizer of the
  stabilizer group, nontrivial logical operators, and logical `X`/`Z` pairs.
- `LogicalOperatorCoset`: the predicate singling out representatives of
  nontrivial cosets of the stabilizer in its centralizer.
- `LogicalGates`: logical gates, and how to recognize one from its conjugation
  action on stabilizer generators.
- `LogicalGateGroup`: the group of unitaries mapping the codespace to itself.
- `LogicalCliffordAction`: logical Hadamard and phase gates on one logical
  qubit.
- `CodeDistance`: code distance, the minimum weight of a nontrivial logical
  operator, and the `[[n, k, d]]` packaging.
-/

module

public import QEC.Stabilizer.Framework.Core.Stabilizer
public import QEC.Stabilizer.Framework.Core.Logical
public import QEC.Stabilizer.Framework.Core.CSS
public import QEC.Stabilizer.Framework.Core.CodeNotation

/-!
# Framework.Core

The abstract stabilizer formalism:

- `Stabilizer`: stabilizer groups, the codespace, the centralizer, and
  stabilizer codes.
- `Logical`: logical operators, logical gates, and code distance.
- `CSS`: Z-type and X-type operators, and distance closers for CSS codes.
- `CodeNotation`: the scoped type notation `Code[[n, k]]`, `Code[[n, k, d]]`
  and `Code[[n, k]]ₗ` for the bundled codes.
-/

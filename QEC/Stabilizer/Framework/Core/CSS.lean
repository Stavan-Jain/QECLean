import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance

/-!
# Core: CSS codes

- `CSSPredicates`: Z-type and X-type Pauli operators and group elements, and
  their closure under the group operations.
- `CSSNoNegI`: Z-type and X-type generators that commute with each other do not
  generate `-I`.
- `CSSCommutationLemmas`: two Z-type elements commute, and so do two X-type
  elements.
- `CSSDistance`: distance-2 and distance-3 closers from anticommute witnesses
  for low-weight Paulis, and their column form for CSS check matrices.
-/

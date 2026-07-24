import QECLight

/-!
# Playground

A scratch file for trying things against QECLean. Edit freely — nothing here
is part of the library, and no `lean_lib` builds it.

It imports `QECLight`, which is the library minus the bivariate-bicycle code
family (too memory-hungry for a container or a shared session; see
`QECLight.lean`). For the gross-code results, use `import QEC` in a local
checkout with the memory to spare.

Put your cursor at the end of a line to see the goal state in the InfoView.
-/

open Quantum.StabilizerGroup

-- The two central definitions: an `[[n, k]]` stabilizer code, and one whose
-- distance has been proved.
#check @StabilizerCode
#check @StabilizerCodeWithDistance
#check @HasCodeDistance

-- A worked result to inspect: Steane ⊗ Steane, an unconditional `[[49, 1, 9]]`
-- concatenated code.
#check Steane7.steaneConcatCodeWithDistance

-- The parametric toric code, for every `L ≥ 2`.
#check @toricHomologicalCode

/-
Your turn. For example:

example : 2 + 2 = 4 := by decide
-/

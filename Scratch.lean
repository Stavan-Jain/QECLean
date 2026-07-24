import QECTutorial

/-!
# Scratch — start here

This is your workspace for the *Lean into QEC* tutorial (QCE26, Toronto).
Edit freely; nothing here is part of the library.

`QECTutorial` is the whole formalization minus the bivariate-bicycle code
family, which is too memory-hungry for a hosted session. Everything below
is available.

Put your cursor at the end of a line to see the goal state in the InfoView
(the panel on the right; `Ctrl/Cmd + Shift + Enter` opens it if it is closed).
-/

open Quantum.StabilizerGroup

-- The two central definitions: an `[[n, k]]` stabilizer code, and one whose
-- distance has been proved.
#check @StabilizerCode
#check @StabilizerCodeWithDistance
#check @HasCodeDistance

-- A worked result you can inspect: Steane ⊗ Steane, an unconditional
-- `[[49, 1, 9]]` concatenated code.
#check Steane7.steaneConcatCodeWithDistance

-- The parametric toric code, for every `L ≥ 2`.
#check @toricHomologicalCode

/-
Your turn. For example:

example : 2 + 2 = 4 := by decide
-/

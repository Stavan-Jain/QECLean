module

public import QECWidgets.PauliEval
public import QECWidgets.Style
public import QECWidgets.PauliStrip
public import QECWidgets.PauliGoalPanel
public import QECWidgets.ToricLattice
public import QECWidgets.CheckMatrix
public import QECWidgets.Demo

/-!
# QECWidgets

ProofWidgets-based infoview widgets for the QEC library: colored per-qubit Pauli
support strips, commutation parity views, and friends. See
`QECWidgets/Demo.lean` for living usage examples.

This library is deliberately separate from `QEC` (same policy as
`QECBlueprint`): only `QECWidgets` imports ProofWidgets, so the mathematical
library keeps its dependency surface unchanged. Everything here is untrusted
display-layer meta code — widgets render what reduction finds, and proofs are
still checked by the kernel as usual.
-/

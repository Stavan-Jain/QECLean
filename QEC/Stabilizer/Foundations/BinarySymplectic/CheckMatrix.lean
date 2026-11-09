import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Check matrix of a list of Pauli group elements

The check matrix of a list of n-qubit Pauli group elements has one row per
element: the symplectic vector of that element's operator part. The elements
are independent generators exactly when the rows are linearly independent over
`ZMod 2` (`rowsLinearIndependent`).
-/

namespace Quantum

variable {n : ℕ}

namespace NQubitPauliGroupElement

/-- The check matrix of a list of n-qubit Pauli group elements: row `i` is the
symplectic vector of the operator part of the `i`-th element, so the first `n`
columns hold `X`-bits and the last `n` columns hold `Z`-bits. -/
def checkMatrix (L : List (NQubitPauliGroupElement n)) :
    Matrix (Fin L.length) (Fin (n + n)) (ZMod 2) :=
  fun i j => NQubitPauliOperator.toSymplectic (L.get i).operators j

/-- The rows of the check matrix of `L` are linearly independent over `ZMod 2`:
no element of `L` is, up to phase, a product of the others. -/
def rowsLinearIndependent (L : List (NQubitPauliGroupElement n)) : Prop :=
  LinearIndependent (ZMod 2) (fun i : Fin L.length => checkMatrix L i)

end NQubitPauliGroupElement

end Quantum

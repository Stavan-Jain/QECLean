import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Foundations.PauliGroup.TransversalConjugation
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.Representation

/-!
# The n-qubit Pauli group

- `NQubitOperator`: n-qubit Pauli operators, their matrices, support and
  weight.
- `NQubitElement`: the group `NQubitPauliGroupElement n`.
- `Notation`: the scoped literal notation `σ[XZIX]` and `P[XZIX]`
  (`open scoped Pauli`).
- `Representation`: the matrix and gate representation, and its faithfulness.
- `Commutation`: commutation, anticommutation and their parity
  characterization.
- `CommutationTactics`: the tactics `pauli_comm_componentwise`,
  `pauli_comm_even_anticommutes` and `pauli_anticomm_odd_anticommutes`.
- `TransversalConjugation`: conjugation of Pauli operators by uniform
  transversal gates.
-/

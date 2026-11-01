import QEC.Stabilizer.Framework.FoldDouble.Basic
import QEC.Stabilizer.Framework.FoldDouble.OperatorImage
import QEC.Stabilizer.Framework.FoldDouble.Groups
import QEC.Stabilizer.Framework.FoldDouble.Distance
import QEC.Stabilizer.Framework.FoldDouble.BBCover

/-!
# Fold and double

The fold-and-double distance theorem for a stabilizer code whose qubits are
paired: the folded code on the pairs, its four phase-free groups `J ≤ P` and
`T ≤ K`, and the theorem that under the floor conditions the distance of the
paired code is exactly twice the distance of the folded code.

- `FoldDouble.Basic` — the phase-free Pauli group, pairings, sheets, the sheet
  swap, fold and double, and their weight and commutation calculus
- `FoldDouble.OperatorImage` — operator images of subgroups of the Pauli group,
  centralizers and nontrivial logicals read on operator parts, and the sign
  choice turning an isotropic phase-free subgroup into a `StabilizerGroup`
- `FoldDouble.Groups` — the four groups, doubling logicals, symmetric pairings,
  the folded code and the floors `d_K`, `d_P`
- `FoldDouble.Distance` — the two kinds of nontrivial logical operator, the
  residual `m_b`, and the distance theorem in its general and symmetric forms
- `FoldDouble.BBCover` — the pairing of a free double cover of
  bivariate-bicycle codes by its deck translation, the dictionary
  `fold = push1`, `double = pull1` on chain operators, and the hypotheses of
  the symmetric theorem that the doubling-theorem inputs supply
-/

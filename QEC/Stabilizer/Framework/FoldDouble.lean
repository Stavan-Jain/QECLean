import QEC.Stabilizer.Framework.FoldDouble.Basic
import QEC.Stabilizer.Framework.FoldDouble.OperatorImage
import QEC.Stabilizer.Framework.FoldDouble.Groups
import QEC.Stabilizer.Framework.FoldDouble.Distance
import QEC.Stabilizer.Framework.FoldDouble.CoverBound
import QEC.Stabilizer.Framework.FoldDouble.Certificates
import QEC.Stabilizer.Framework.FoldDouble.BBCover

/-!
# Fold and double

A pairing of the qubits of a stabilizer code folds a Pauli operator onto the
pairs, by multiplying the two members of each pair, and doubles an operator on
the pairs, by placing it on both members. The fold-and-double distance theorem
compares the paired code with its folded code on the pairs: under floor
conditions on four groups of operators on the pairs, the distance of the
paired code is exactly twice the least weight of a doubling logical.

- `Basic`: the phase-free Pauli group, pairings, sheets, the sheet swap, fold
  and double, and their weight and commutation rules.
- `OperatorImage`: operator images of subgroups of the Pauli group,
  centralizers and nontrivial logical operators read on operator parts, and
  the choice of signs turning an isotropic phase-free subgroup into a
  `StabilizerGroup`.
- `Groups`: the four groups `J ≤ P` and `T ≤ K`, doubling logicals, symmetric
  pairings, the folded code, and the floors `d_K` and `d_P`.
- `Distance`: the two kinds of nontrivial logical operator, the residual
  `m_b`, and the distance theorem in its general, sector and symmetric forms.
- `CoverBound`: for a symmetric pairing, the lower bound
  `min φ (min (2 d) ρ)` from the three possible folds of a logical operator,
  the matching upper bound, and the symmetric distance theorem with its last
  hypothesis in weight form and without the witness hypothesis.
- `Certificates`: the averaging argument and the single-type certificates, one
  or two clean checks, for condition (J).
- `BBCover`: the pairing of a free double cover of bivariate bicycle codes by
  its deck translation, the dictionary `fold = push1`, `double = pull1` on
  chain operators, and the doubling theorem for the cover as an instance of
  the distance theorem.
-/

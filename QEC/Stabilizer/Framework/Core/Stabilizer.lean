module

public import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
public import QEC.Stabilizer.Framework.Core.Stabilizer.Codespace
public import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
public import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
public import QEC.Stabilizer.Framework.Core.Stabilizer.GeneratorListLemmas
public import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
public import QEC.Stabilizer.Framework.Core.Stabilizer.CodespaceDimension

/-!
# Core: stabilizer groups and codes

- `StabilizerGroup`: stabilizer groups, stabilized vectors and states, and
  codespace membership.
- `Codespace`: the codespace as a submodule, the stabilizer sum, and the
  existence of a codespace state.
- `Centralizer`: the centralizer of a stabilizer group, which is also its
  normalizer in the Pauli group.
- `SubgroupLemmas`: group-theoretic lemmas about `Subgroup.closure`.
- `GeneratorListLemmas`: generator lists indexed by a square grid.
- `StabilizerCode`: `StabilizerCode n k`, `StabilizerCodeWithLogicals n k`, and
  stabilizer groups built from generator lists.
- `CodespaceDimension`: the codespace of an `[[n, k]]` code has dimension
  `2 ^ k`.
-/

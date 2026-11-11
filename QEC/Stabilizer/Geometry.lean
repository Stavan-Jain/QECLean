import QEC.Stabilizer.Geometry.FinPeriodic
import QEC.Stabilizer.Geometry.GridIndexing
import QEC.Stabilizer.Geometry.CellComplexTypes

/-!
# Geometry

Lattice primitives shared by the lattice code families:

- `FinPeriodic`: cyclic successor and predecessor on `Fin L` (`next`, `prev`),
  with functions and sums on the cycle `Fin L`.
- `GridIndexing`: injectivity of the row-major encoding of grid coordinates.
- `CellComplexTypes`: vertex, edge and face indices of an `L × L` periodic
  square lattice, and the chain groups over `ZMod 2`.
-/

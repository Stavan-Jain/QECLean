import QEC.Stabilizer.Geometry.FinPeriodic
import QEC.Stabilizer.Geometry.GridIndexing
import QEC.Stabilizer.Geometry.CellComplexTypes

/-!
# Geometry

Lattice-family-agnostic geometric primitives:
- `FinPeriodic`: modular arithmetic on `Fin L` (`next`, `prev`)
- `GridIndexing`: row-major / column-major coordinate encodings
- `CellComplexTypes`: abstract `EdgeIdx`, `FaceIdx`, `VtxIdx` and chain types
-/

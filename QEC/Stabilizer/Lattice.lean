-- Deprecated: `QEC.Stabilizer.Lattice` was split across `QEC.Stabilizer.Geometry`
-- (lattice-agnostic primitives) and `QEC.Stabilizer.Codes.{Toric,RotatedSurface}`
-- (family-specific lattice content). This shim will be removed in a follow-up release.
import QEC.Stabilizer.Geometry
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface

import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations
import QEC.Stabilizer.Geometry
import QEC.Stabilizer.Framework
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface
import QEC.Stabilizer.Codes.Color
import QEC.Stabilizer.Codes.Repetition
import QEC.Stabilizer.Codes.Iceberg
import QEC.Stabilizer.Codes.Small

/-!
# QECLight — compatibility import surface

This entry point predates the extraction of the large bivariate-bicycle
certificate proofs into `bb-distance-lean`. It remains available to existing
hosted-editor configurations. Both `QECLight` and `QEC` now leave those
concrete distance proofs to the downstream package; the general BB foundations
remain part of `Framework`.
-/

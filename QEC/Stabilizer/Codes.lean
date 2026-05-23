import QEC.Stabilizer.Codes._TEMPLATE
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface
import QEC.Stabilizer.Codes.Repetition
import QEC.Stabilizer.Codes.Small

/-!
# Codes

Concrete stabilizer codes, organized by family:
- `Toric`          — parametric toric code (code + lattice + homology)
- `RotatedSurface` — rotated surface code (code + lattice + homology)
- `Repetition`     — classical repetition codes
- `Small`          — single-instance codes (Shor9, Steane7, [[5,1,3]], …)

`_TEMPLATE.lean` is the canonical structural reference for drafting new codes.
-/

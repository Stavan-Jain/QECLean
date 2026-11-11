import QEC.Stabilizer.Codes._TEMPLATE
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface
import QEC.Stabilizer.Codes.Color
import QEC.Stabilizer.Codes.Repetition
import QEC.Stabilizer.Codes.Iceberg
import QEC.Stabilizer.Codes.BivariateBicycle
import QEC.Stabilizer.Codes.Small
import QEC.Stabilizer.Codes.Concat

/-!
# Codes

Concrete stabilizer codes, by family:

- `Small`: single codes on a fixed number of qubits (the `[[4, 1, 2]]`,
  `[[4, 2, 2]]`, `[[6, 2, 2]]`, `[[5, 1, 3]]`, Steane `[[7, 1, 3]]` and Shor
  `[[9, 1, 3]]` codes) and the quantum Hamming family.
- `Repetition`: the repetition codes.
- `Iceberg`: the `[[2m, 2m − 2, 2]]` iceberg codes.
- `Toric`: the `L × L` toric code.
- `RotatedSurface`: the rotated surface code.
- `Color`: the triangular honeycomb color codes.
- `BivariateBicycle`: the bivariate bicycle codes.
- `Concat`: concatenated codes, instances of `Framework/Concatenation` (the
  concatenated Steane code `[[49, 1, 9]]`).
- `_TEMPLATE`: the structure every code file follows.
-/

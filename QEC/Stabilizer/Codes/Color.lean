import QEC.Stabilizer.Codes.Color.Geometry
import QEC.Stabilizer.Codes.Color.FaceParity
import QEC.Stabilizer.Codes.Color.Orthogonality
import QEC.Stabilizer.Codes.Color.Independence
import QEC.Stabilizer.Codes.Color.Code
import QEC.Stabilizer.Codes.Color.Logicals
import QEC.Stabilizer.Codes.Color.Boundary
import QEC.Stabilizer.Codes.Color.BinaryLogical
import QEC.Stabilizer.Codes.Color.Energy
import QEC.Stabilizer.Codes.Color.Spin
import QEC.Stabilizer.Codes.Color.SpinSum
import QEC.Stabilizer.Codes.Color.LowerBound
import QEC.Stabilizer.Codes.Color.Distance

/-!
# Triangular honeycomb color codes

The family of triangular color codes of parameter `r`, with parameters
`[[3r(r+1) + 1, 1, 2r + 1]]`:

- `Geometry`: the lattice of the patch, the index types `Qubit r` and
  `Face r`, their counts, and the indicator vectors `incidence` of the faces.
- `FaceParity`: every face has an even number of qubits.
- `Orthogonality`: two faces share an even number of qubits, so the indicator
  vectors of the faces are mutually orthogonal.
- `Independence`: the indicator vectors of the faces are linearly independent.
- `Code`: the stabilizer code `stabilizerCode r` and its self-dual CSS chain
  complex `homologicalCode r`.
- `Logicals`: the transversal logical X and Z operators.
- `Boundary`: the left side of the patch, a cycle of weight `2r + 1` that is
  not a boundary.
- `BinaryLogical`: the boundaries are the cycles of even parity, and the
  cycles of odd parity are the all-ones chain plus the boundaries.
- `Energy`: the shell inequality, a lower bound for the weight of one layer
  of the patch in terms of face labels.
- `Spin`: the values of the all-ones chain plus a combination of face checks,
  in terms of the face labels.
- `SpinSum`: the weight of that chain as a sum of layer weights.
- `LowerBound`: every cycle of odd parity has weight at least `2r + 1`.
- `Distance`: the distance is `2r + 1`, and the code with all its parameters.
-/

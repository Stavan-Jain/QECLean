module

public import QEC.Stabilizer.Codes.RotatedSurface.CellComplex
public import QEC.Stabilizer.Codes.RotatedSurface.BoundaryMaps
public import QEC.Stabilizer.Codes.RotatedSurface.ChainComplex
public import QEC.Stabilizer.Codes.RotatedSurface.H1Dimension
public import QEC.Stabilizer.Codes.RotatedSurface.N
public import QEC.Stabilizer.Codes.RotatedSurface.StabilizerCode
public import QEC.Stabilizer.Codes.RotatedSurface.DistanceX
public import QEC.Stabilizer.Codes.RotatedSurface.DistanceZ
public import QEC.Stabilizer.Codes.RotatedSurface.Distance

/-!
# The rotated surface code

The `[[L * L, 1, L]]` rotated surface code on the `L × L` grid, for every odd
`L ≥ 3`.

* `CellComplex`: the qubits, the Z-checks and the X-checks of the grid, and
  the set of qubits each check acts on.
* `BoundaryMaps`: the boundary maps `∂₂`, `∂₁`, the cut map `δ⁰` and the
  chain-complex law.
* `ChainComplex`: the cycles `Z₁ L`, the boundaries `B₁ L`, the homology
  `H₁ L`, and the chain complex as a `HomologicalCode`.
* `H1Dimension`: the checks are independent and `dim H₁ = 1`.
* `N`: the Z- and X-checks as Pauli operators and the stabilizer group.
* `StabilizerCode`: the rotated surface code as a `StabilizerCode` with one
  logical qubit, and its logical operators on the middle column and the
  middle row.
* `DistanceX`, `DistanceZ`: a cycle that is not a boundary, and a dual cycle
  that is not a dual boundary, has weight at least `L`, and the logical
  operators have weight `L`.
* `Distance`: the code distance is `L`.
-/

import QEC.Stabilizer.Codes.Toric.Chains
import QEC.Stabilizer.Codes.Toric.BoundaryMaps
import QEC.Stabilizer.Codes.Toric.Homology
import QEC.Stabilizer.Codes.Toric.OperatorChains
import QEC.Stabilizer.Codes.Toric.ChainComplex
import QEC.Stabilizer.Codes.Toric.ChainOps
import QEC.Stabilizer.Codes.Toric.H1Dimension
import QEC.Stabilizer.Codes.Toric.WrappingInvariants
import QEC.Stabilizer.Codes.Toric.DualWrappingInvariants
import QEC.Stabilizer.Codes.Toric.CodeN
import QEC.Stabilizer.Codes.Toric.LogicalCorrespondenceX
import QEC.Stabilizer.Codes.Toric.LogicalCorrespondenceZ
import QEC.Stabilizer.Codes.Toric.DistanceX
import QEC.Stabilizer.Codes.Toric.DistanceZ
import QEC.Stabilizer.Codes.Toric.StabilizerCode
import QEC.Stabilizer.Codes.Toric.Distance
import QEC.Stabilizer.Codes.Toric.RankCertificate

/-!
# The toric code

The `[[2 * L * L, 2, L]]` toric code on the `L × L` periodic square lattice,
for every `2 ≤ L`.

* `Chains`: indicator chains, support and weight of 1-chains.
* `BoundaryMaps`: the boundary maps `∂₂`, `∂₁`, the vertex cut map `δ⁰` and
  the chain-complex law.
* `Homology`: the cycles `Z₁ L`, the boundaries `B₁ L` and the homology
  `H₁ L`.
* `OperatorChains`: the numbering of the edges as qubits and the X- and Z-type
  operators of a 1-chain.
* `ChainComplex`: the chain complex as a `HomologicalCode`.
* `ChainOps`: algebra and weight of the chain operators.
* `H1Dimension`: `dim H₁ = 2`.
* `WrappingInvariants`: the wrapping numbers of a cycle, the isomorphism
  `H₁ ≃ (ZMod 2)²`, and the weight bound `L` for cycles that are not
  boundaries.
* `DualWrappingInvariants`: the dual complex, the duality of the lattice, the
  wrapping numbers of a dual cycle, and the weight bound `L` for dual cycles
  that are not dual boundaries.
* `CodeN`: the vertex and face checks and the stabilizer group.
* `LogicalCorrespondenceX`, `LogicalCorrespondenceZ`: X-type logical operators
  are the cycles modulo boundaries, and Z-type logical operators are the dual
  cycles modulo dual boundaries.
* `DistanceX`, `DistanceZ`: a nontrivial X-type or Z-type logical operator has
  weight at least `L`, and weight `L` is attained.
* `StabilizerCode`: the toric code as a `StabilizerCode` with two logical
  qubits, presented by an independent list of checks, and its logical
  operators.
* `Distance`: the code distance is `L`.
* `RankCertificate`: independence of the checks for `L = 4, 5, 6` by rank
  certificates.
-/

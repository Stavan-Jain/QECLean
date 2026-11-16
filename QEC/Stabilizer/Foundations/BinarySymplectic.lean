module

public import QEC.Stabilizer.Foundations.BinarySymplectic.Core
public import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
public import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
public import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
public import QEC.Stabilizer.Foundations.BinarySymplectic.RankCertificate

/-!
# Binary symplectic representation and check matrices

- `Core`: `PauliOperator.toSymplecticSingle` and
  `NQubitPauliOperator.toSymplectic`.
- `SymplecticInner`: the symplectic inner product and its relation to
  commutation (`commutes_iff_symplectic_inner_zero`).
- `CheckMatrix`: `NQubitPauliGroupElement.checkMatrix` and
  `rowsLinearIndependent`.
- `CheckMatrixDecidable`: the exhaustive `Decidable` instance for
  `rowsLinearIndependent`.
- `RankCertificate`: polynomial-time independence certificates
  (`rowsLinearIndependent_of_rankCertCheck`).

The results relating these to stabilizer groups are in
`QEC.Stabilizer.Framework.Symplectic`.
-/

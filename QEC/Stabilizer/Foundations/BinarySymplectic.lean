import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.BinarySymplectic.RankCertificate

/-!
# Binary symplectic representation and check matrix (Foundations)

Pure binary-symplectic algebra. Re-exports:

- **Core**: `PauliOperator.toSymplecticSingle`,
  `NQubitPauliOperator.toSymplectic`
- **SymplecticInner**: `symplecticInner`, `commutes_iff_symplectic_inner_zero`,
  `toSymplectic_add`
- **CheckMatrix**: `NQubitPauliGroupElement.checkMatrix`,
  `rowsLinearIndependent`
- **CheckMatrixDecidable**: `Decidable (rowsLinearIndependent L)` and
  `rowsLinearIndependent_iff_forall`
- **RankCertificate**: polynomial-time independence certificates —
  `rowsLinearIndependent_of_mul_eq_one`, `rankCertCheck`,
  `rowsLinearIndependent_of_rankCertCheck`

For the stabilizer-aware bridge content (`IndependentEquiv`,
`SymplecticOrthogonal`, `SymplecticSpan`, `WeightTwoInSpan`, `SupportLemmas`),
see `QEC.Stabilizer.Framework.Symplectic`.
-/

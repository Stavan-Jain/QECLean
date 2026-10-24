import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineFastMaps
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.FiberData
import QEC.Stabilizer.Framework.Homological.Certificate.MaskedAffine

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData

/-- Every short top lift of this middle shadow is a boundary. -/
noncomputable def TopFiberBoundary (beta : Nat) : Prop := ∀ word : Nat, word < 2^180 →
  reconX topEColumns word = reconX topRColumns beta →
  bitCount 180 (outsideMask word beta) ≤ (22-bitCount 180 beta)/2 →
  ∃ coefficient : Nat, reconX boundaryColumns coefficient = topJoin word beta

end Quantum.Stabilizer.Homological.BB.Bravyi360

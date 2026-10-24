import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.AffineFastMaps
import QEC.Stabilizer.Framework.Homological.Certificate.PackedSlice

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
/-- Every top boundary and embedding column fits the common 512-bit packed lane. -/
theorem affineBoundaryMaps_bounded :
    (∀ p ∈ topBoundaryFast, p.1 < 512 ∧ p.2 < 2^512) ∧
    (∀ p ∈ topLeftFast, p.1 < 512 ∧ p.2 < 2^512) ∧
    (∀ p ∈ topRightFast, p.1 < 512 ∧ p.2 < 2^512) := by decide +kernel
end Quantum.Stabilizer.Homological.BB.Bravyi360

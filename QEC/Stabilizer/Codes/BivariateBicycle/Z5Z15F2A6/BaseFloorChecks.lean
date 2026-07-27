/-
# A21: the small-cycle bundle obligations for the `[[150,8,8]]` base

The four finite obligations of `SmallCycleData` for `(a150, b150)`,
discharged by `native_decide` (BB108/BB90/Z6Z14 pattern).  Note this
instance is OUTSIDE the A16 class ((iii) fails — `A = 1+x+y` is
monomial in both parity projections), so the finite checks are doing
real per-instance work here, not just certifying a class member.

Kept as a leaf module: `check_four` sweeps `2·150³ ≈ 6.75M` tuples
(≈ 10 min of `native_decide`), and per-file recompiles re-pay that
cost — iterate in `BaseFloor.lean`, not here.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Defs
import QEC.Stabilizer.Framework.Homological.BBSmallCycle

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-- `ε(A) = 1`. -/
lemma epsA_holds : ∑ h : G150, a150 h = 1 := by native_decide

/-- `ε(B) = 1`. -/
lemma epsB_holds : ∑ h : G150, b150 h = 1 := by native_decide

/-- No normalized weight-2 cycle. -/
lemma check_two_holds : ∀ b : Fin 2, ∀ q : G150 × Fin 2,
    q ≠ ((0 : G150), b) →
    ∃ h : G150, SmallCycle.termAt a150 b150 ((0 : G150), b) h
      + SmallCycle.termAt a150 b150 q h ≠ 0 := by
  native_decide

/-- No normalized weight-4 cycle (tuple form; colliding tuples cancel to
the weight-2 shape). -/
lemma check_four_holds : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : G150 × Fin 2,
    q₁ = ((0 : G150), b) ∨ q₂ = ((0 : G150), b) ∨
    q₃ = ((0 : G150), b) ∨
    ∃ h : G150, SmallCycle.termAt a150 b150 ((0 : G150), b) h
      + SmallCycle.termAt a150 b150 q₁ h
      + SmallCycle.termAt a150 b150 q₂ h
      + SmallCycle.termAt a150 b150 q₃ h ≠ 0 := by
  native_decide

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum

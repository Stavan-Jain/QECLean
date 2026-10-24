import QEC.Stabilizer.Framework.Homological.Certificate.SearchCertificate
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Adjoints
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestCheck

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData

/-- The available outside budget for a shallow fiber. -/
noncomputable def outsideBudget (r : Fiber) : Nat := (22-r.weight)/2

/-- Matching scalar metadata transfers a checked outside census to a canonical forest record. -/
theorem search_census_transfer (r : Fiber) (beta cap : Nat) (allowed : List Nat)
    (hcomplete : ∀ {word : Nat}, word < 2^90 →
      reconX bottomEColumns word = reconX bottomRColumns beta →
      bitCount 90 (outsideMask word beta) ≤ cap → outsideMask word beta ∈ allowed)
    (hmatch : r.beta = beta ∧ outsideBudget r = cap ∧ r.seeds.map Seed.off = allowed)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ outsideBudget r) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  obtain ⟨hb,hc,hs⟩ := hmatch
  rw [hb] at he
  rw [hb,hc] at hoff
  rw [hb,hs]
  exact hcomplete hw he hoff

namespace HighSearch

/-- The full bottom transpose fits in the 256-bit search lanes. -/
theorem transpose_bounded : ∀ p ∈ bottomETransposeColumns, p.1 < 256 ∧ p.2 < 2^256 := by
  decide +kernel

end HighSearch
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest

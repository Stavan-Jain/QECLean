import QEC.Stabilizer.Codes.Color.BinaryLogical
import QEC.Stabilizer.Codes.Color.SpinSum

/-!
# The lower bound on the weight of the odd cycles of the color code

The shell inequality `energy_shell_lower_bound`, applied layer by layer, bounds
the energy of the apex and the first `r` layers below by `potentialPhi r` of
the next row of face labels (`potentialPhi_le_spinEnergy`). For the patch of
parameter `r` that row is zero, so the energy is at least `distance r`
(`distance_le_spinEnergy`). Since the energy is the weight of the all-ones
chain plus a combination of face checks, and every cycle of odd parity has
this form, every cycle of odd parity has weight at least `distance r`
(`odd_cycle_weight_lower_bound`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The energy of the apex and the first `r` layers is at least `potentialPhi`
of the first row of face labels of the next layer, provided the labels
`B l (l + 1)` beyond the end of their rows are `0`. -/
theorem potentialPhi_le_spinEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ)
    (hB : ∀ l < r, B l (l + 1) = 0) :
    potentialPhi r (A r) ≤ spinEnergy A B C r := by
  induction r with
  | zero => simp [potentialPhi, spinEnergy]
  | succ r ih =>
    rw [spinEnergy, Finset.sum_range_succ, ← add_assoc]
    exact (energy_shell_lower_bound r (A r) (B r) (C r) _ (A (r + 1)) (hB r r.lt_succ_self)).trans
      (Nat.add_le_add_right (ih fun l hl => hB l (hl.trans r.lt_succ_self)) _)

/-- A configuration of face labels that vanish outside the patch has energy at
least `distance r`. -/
theorem distance_le_spinEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ)
    (hB : ∀ l < r, B l (l + 1) = 0) (hA : A r = fun _ => 0) :
    distance r ≤ spinEnergy A B C r := by
  have h := potentialPhi_le_spinEnergy A B C r hB
  rwa [hA, potentialPhi_zero] at h

/-- The all-ones chain plus a combination of face checks has weight at least
`distance r`. -/
lemma allOnes_add_checkCombination_weight_lower_bound {r : ℕ}
    (a : Face r → ZMod 2) :
    distance r ≤ (homologicalCode r).chainWeight
      (allOnes r + SelfDual.checkCombination (@incidence r) a) := by
  rw [chainWeight_allOnes_add_checkCombination_eq_spinEnergy]
  exact distance_le_spinEnergy _ _ _ r (fun l _ => faceBit_of_column_ge a 1 l (l + 1) le_rfl)
    (funext fun j => faceBit_of_layer_ge a 0 r j le_rfl)

/-- Every cycle of odd parity has weight at least `distance r`. -/
theorem odd_cycle_weight_lower_bound {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles) (hodd : ∑ q, c q = 1) :
    distance r ≤ (homologicalCode r).chainWeight c := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := (odd_cycle_iff_allOnes_add_boundary c).mp ⟨hc, hodd⟩
  exact allOnes_add_checkCombination_weight_lower_bound a

end Quantum.StabilizerGroup.ColorCode

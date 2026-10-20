import QEC.Stabilizer.Codes.Color.BinaryLogical
import QEC.Stabilizer.Codes.Color.SpinSum

/-!
# The distance lower bound for triangular color codes

A face-check combination gives three rows of binary labels at every layer
of the honeycomb patch. The shell-energy inequality propagates a lower
bound through all layers. The final external row is zero, so the resulting
bound is `2r + 1`. The binary logical classification then applies it to
every odd cycle, with no assumption about the distance.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The energy of a prefix of the triangular patch, with a chosen external
row of face labels along its bottom boundary. -/
def prefixEnergy (A B C : ℕ → ℕ → ZMod 2) : ℕ → (ℕ → ZMod 2) → ℕ
  | 0, t => (1 + t 0).val
  | n + 1, t => prefixEnergy A B C n (A n) +
      shellEnergy (n + 1) (A n) (B n) (C n)
        (if n = 0 then fun _ => 0 else C (n - 1)) t

/-- Each shell preserves the lower bound determined by the external row
of face labels. -/
theorem potentialPhi_le_prefixEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ)
    (hB : ∀ l < r, B l (l + 1) = 0) (t : ℕ → ZMod 2) :
    potentialPhi r t ≤ prefixEnergy A B C r t := by
  revert hB t
  induction r with
  | zero =>
      intro _ t
      simp [potentialPhi, prefixEnergy]
  | succ r ih =>
      intro hB t
      have hprevious : potentialPhi r (A r) ≤ prefixEnergy A B C r (A r) :=
        ih (fun l hl => hB l (Nat.lt_trans hl (Nat.lt_succ_self r))) (A r)
      exact (energy_shell_lower_bound r (A r) (B r) (C r)
        (if r = 0 then fun _ => 0 else C (r - 1)) t
        (hB r (Nat.lt_succ_self r))).trans (Nat.add_le_add_right hprevious _)

/-- Expanding the prefix recursion gives the apex contribution and the
sum of the successive three-row shell energies. -/
theorem prefixEnergy_eq_spinEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ) :
    prefixEnergy A B C r (A r) = spinEnergy A B C r := by
  induction r with
  | zero => simp [prefixEnergy, spinEnergy]
  | succ r ih =>
      simp only [prefixEnergy, spinEnergy, Finset.sum_range_succ] at ih ⊢
      omega

/-- A triangular spin configuration with no face labels outside the patch
has energy at least the odd distance parameter. -/
theorem distance_le_spinEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ)
    (hB : ∀ l < r, B l (l + 1) = 0) (hA : A r = fun _ => 0) :
    distance r ≤ spinEnergy A B C r := by
  have h := potentialPhi_le_prefixEnergy A B C r hB (A r)
  rw [prefixEnergy_eq_spinEnergy, hA, potentialPhi_zero] at h
  exact h

/-- Every representative of the all-ones binary logical class has weight
at least the distance parameter of the triangular patch. -/
theorem allOnes_add_checkCombination_weight_lower_bound {r : ℕ}
    (a : Face r → ZMod 2) :
    distance r ≤ (homologicalCode r).chainWeight
      (allOnes r + SelfDual.checkCombination (@incidence r) a) := by
  rw [chainWeight_allOnes_add_checkCombination_eq_spinEnergy]
  apply distance_le_spinEnergy
  · intro l _
    exact faceBit_of_column_ge a 1 l (l + 1) le_rfl
  · funext j
    exact faceBit_of_layer_ge a 0 r j le_rfl

/-- Every odd zero-syndrome chain has weight at least `2r + 1`. -/
theorem odd_cycle_weight_lower_bound {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles) (hodd : ∑ q, c q = 1) :
    distance r ≤ (homologicalCode r).chainWeight c := by
  obtain ⟨b, hb, heq⟩ := (odd_cycle_iff_allOnes_add_boundary c).mp ⟨hc, hodd⟩
  obtain ⟨a, ha⟩ := hb
  rw [heq, ← ha]
  exact allOnes_add_checkCombination_weight_lower_bound (r := r) a

end Quantum.StabilizerGroup.ColorCode

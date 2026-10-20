import QEC.Stabilizer.Codes.Color.Geometry

/-!
# A finite local energy certificate for triangular color-code shells

The three rows added to a triangular patch admit a uniform lower bound on
their binary Hamming weight. The proof telescopes an eight-state potential;
its initial, transition, and terminal inequalities are finite statements
proved by kernel reduction. No bound on the size of the patch is assumed.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- The cost of a bottom boundary with an external row of face labels. -/
def potentialPhi (n : ℕ) (t : ℕ → ZMod 2) : ℕ :=
  2 * (∑ j ∈ Finset.range n, (1 + t j).val) + (1 + t n).val

/-- Four shell sites around adjacent labels in the middle face row. -/
def fourBitCost (A B C t : ℕ → ZMod 2) (j : ℕ) : ℕ :=
  (1 + C j + A j + B j).val +
  (1 + C j + A j + B (j + 1)).val +
  (1 + C j + B j + t j).val +
  (1 + C j + B (j + 1) + t (j + 1)).val

/-- Two upper shell sites whose common labels cancel in their binary sum. -/
def aPairCost (A B s : ℕ → ZMod 2) (j : ℕ) : ℕ :=
  (1 + s j + A j + B (j + 1)).val +
  (1 + s j + A (j + 1) + B (j + 1)).val

/-- The Hamming energy of the three qubit rows in a shell of width `m`.
The last label `B m` is required to vanish when the shell inequality is used. -/
def shellEnergy (m : ℕ) (A B C s t : ℕ → ZMod 2) : ℕ :=
  (1 + A 0 + B 0).val + (1 + B 0 + t 0).val +
  (∑ j ∈ Finset.range m, fourBitCost A B C t j) +
  (∑ j ∈ Finset.range (m - 1), aPairCost A B s j)

/-- The eight-state potential used to telescope the shell-energy inequality. -/
def stripPotential (a b t : ZMod 2) : ℕ :=
  if a = 0 then
    if b = 0 then 1 + (1 + t).val else t.val
  else (1 + t).val

/-- The potential at the left endpoint is paid for by its two shell sites. -/
private theorem stripPotential_initial (a b t : ZMod 2) :
    stripPotential a b t ≤ (1 + a + b).val + (1 + b + t).val := by
  revert a b t
  decide

/-- The eight-state potential satisfies the local transition inequality. -/
private theorem stripPotential_transition (a b t a' b' t' c : ZMod 2) :
    stripPotential a' b' t' + 2 * (1 + t).val ≤
      stripPotential a b t +
      ((1 + c + a + b).val + (1 + c + a + b').val +
        (1 + c + b + t).val + (1 + c + b' + t').val) +
      (a + a').val + 2 * (1 + a).val := by
  revert a b t a' b' t' c
  decide

/-- The final potential pays for the last two boundary entries. -/
private theorem stripPotential_terminal (a b t t' c : ZMod 2) :
    2 * (1 + t).val + (1 + t').val ≤
      stripPotential a b t +
      ((1 + c + a + b).val + (1 + c + a + 0).val +
        (1 + c + b + t).val + (1 + c + 0 + t').val) +
      (1 + a).val := by
  revert a b t t' c
  decide

/-- Two sites containing a pair of labels bound their binary difference. -/
private theorem pair_difference_le (a a' b s : ZMod 2) :
    (a + a').val ≤ (1 + s + a + b).val + (1 + s + a' + b).val := by
  revert a a' b s
  decide

/-- Summing the local transitions leaves only the endpoint potential. -/
private theorem stripPotential_path (n : ℕ) (A B C s t : ℕ → ZMod 2) :
    stripPotential (A n) (B n) (t n) +
        2 * (∑ j ∈ Finset.range n, (1 + t j).val) ≤
      stripPotential (A 0) (B 0) (t 0) +
        (∑ j ∈ Finset.range n, fourBitCost A B C t j) +
        (∑ j ∈ Finset.range n, aPairCost A B s j) +
        2 * (∑ j ∈ Finset.range n, (1 + A j).val) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ht := stripPotential_transition
        (A n) (B n) (t n) (A (n + 1)) (B (n + 1)) (t (n + 1)) (C n)
      have hp := pair_difference_le (A n) (A (n + 1)) (B (n + 1)) (s n)
      change (A n + A (n + 1)).val ≤ aPairCost A B s n at hp
      change stripPotential (A (n + 1)) (B (n + 1)) (t (n + 1)) +
          2 * (1 + t n).val ≤
        stripPotential (A n) (B n) (t n) + fourBitCost A B C t n +
          (A n + A (n + 1)).val + 2 * (1 + A n).val at ht
      simp only [Finset.sum_range_succ]
      omega

/-- A three-row shell preserves the exact boundary-energy lower bound. -/
theorem energy_shell_lower_bound (n : ℕ) (A B C s t : ℕ → ZMod 2)
    (hB : B (n + 1) = 0) :
    potentialPhi (n + 1) t ≤ potentialPhi n A + shellEnergy (n + 1) A B C s t := by
  have hp := stripPotential_path n A B C s t
  have hi := stripPotential_initial (A 0) (B 0) (t 0)
  have ht := stripPotential_terminal (A n) (B n) (t n) (t (n + 1)) (C n)
  have ht' : 2 * (1 + t n).val + (1 + t (n + 1)).val ≤
      stripPotential (A n) (B n) (t n) + fourBitCost A B C t n +
        (1 + A n).val := by
    simpa only [fourBitCost, hB] using ht
  simp only [potentialPhi, shellEnergy, Nat.add_sub_cancel, Finset.sum_range_succ]
  omega

/-- A zero external row has boundary energy equal to the odd code distance. -/
@[simp] theorem potentialPhi_zero (n : ℕ) :
    potentialPhi n (fun _ => 0) = 2 * n + 1 := by
  simp [potentialPhi, show (1 : ZMod 2).val = 1 from rfl]

end Quantum.StabilizerGroup.ColorCode

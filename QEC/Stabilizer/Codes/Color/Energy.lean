import QEC.Stabilizer.Codes.Color.Geometry

/-!
# The shell inequality for the distance of the color code

A chain in the coset of the all-ones chain modulo the face checks is given by
a label in `ZMod 2` on every face. Its value at a qubit, the *spin* of the
qubit, is `1` plus the sum of the labels of the faces containing the qubit,
and its weight is its *energy*, the number of qubits of spin `1`.

This file bounds the energy of one layer of the patch (three rows of qubits)
in terms of rows of face labels, which are functions `ℕ → ZMod 2` of the
position in the row: the three rows `A`, `B`, `C` of the layer, the last row
`s` of the previous layer and the first row `t` of the next layer.

* `shellEnergy m A B C s t` is the energy of a layer with `m` faces per row.
* `potentialPhi n t` is a lower bound for the energy of the apex and the first
  `n` layers when the first row of labels of the next layer is `t`; it is
  `2 * n + 1` for `t = 0` (`potentialPhi_zero`).
* `energy_shell_lower_bound`: adding a layer preserves the bound,
  `potentialPhi (n + 1) t ≤ potentialPhi n A + shellEnergy (n + 1) A B C s t`.

The inequality is proved by a sweep along the layer with the potential
`stripPotential`, a function of the labels `A j`, `B j`, `t j` at one
position. The inequalities for the first step, a middle step and the last step
of the sweep involve finitely many labels and are checked by `decide`.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- The lower bound for the energy of the apex and the first `n` layers, as a
function of the first row `t` of face labels of the next layer. -/
def potentialPhi (n : ℕ) (t : ℕ → ZMod 2) : ℕ :=
  2 * (∑ j ∈ Finset.range n, (1 + t j).val) + (1 + t n).val

/-- The energy of the four qubits of a layer on the face labelled `C j`: two
in the middle row and two in the last row of qubits. -/
def fourBitCost (A B C t : ℕ → ZMod 2) (j : ℕ) : ℕ :=
  (1 + C j + A j + B j).val +
  (1 + C j + A j + B (j + 1)).val +
  (1 + C j + B j + t j).val +
  (1 + C j + B (j + 1) + t (j + 1)).val

/-- The energy of the two qubits of the first row of a layer on the face
labelled `s j` of the previous layer. -/
def aPairCost (A B s : ℕ → ZMod 2) (j : ℕ) : ℕ :=
  (1 + s j + A j + B (j + 1)).val +
  (1 + s j + A (j + 1) + B (j + 1)).val

/-- The energy of the three rows of qubits of a layer with `m` faces per row,
in terms of the rows `A`, `B`, `C` of face labels of the layer, the last row
`s` of the previous layer and the first row `t` of the next layer. The first
two terms are the leftmost qubits of the first and of the last row. The label
`B m` is beyond the end of its row and is `0` for a layer of the patch. -/
def shellEnergy (m : ℕ) (A B C s t : ℕ → ZMod 2) : ℕ :=
  (1 + A 0 + B 0).val + (1 + B 0 + t 0).val +
  (∑ j ∈ Finset.range m, fourBitCost A B C t j) +
  (∑ j ∈ Finset.range (m - 1), aPairCost A B s j)

/-- The potential of the sweep along a layer, as a function of the labels
`A j`, `B j` and `t j` at one position. -/
def stripPotential (a b t : ZMod 2) : ℕ :=
  if a = 0 then
    if b = 0 then 1 + (1 + t).val else t.val
  else (1 + t).val

/-- First step of the sweep: the potential at position `0` is at most the
energy of the two leftmost qubits of the layer. -/
private lemma stripPotential_initial (a b t : ZMod 2) :
    stripPotential a b t ≤ (1 + a + b).val + (1 + b + t).val := by
  decide +revert

/-- Middle step of the sweep: the potential at position `j + 1` plus the term
`2 * (1 + t j).val` of `potentialPhi (n + 1) t` is at most the potential at
position `j` plus the energy of the four qubits on the face labelled `C j`,
the value of `A j + A (j + 1)` and the term `2 * (1 + A j).val` of
`potentialPhi n A`. -/
private lemma stripPotential_transition (a b t a' b' t' c : ZMod 2) :
    stripPotential a' b' t' + 2 * (1 + t).val ≤
      stripPotential a b t +
      ((1 + c + a + b).val + (1 + c + a + b').val +
        (1 + c + b + t).val + (1 + c + b' + t').val) +
      (a + a').val + 2 * (1 + a).val := by
  decide +revert

/-- Last step of the sweep: the last two terms of `potentialPhi (n + 1) t` are
at most the potential at the last position `n` plus the energy of the four
qubits on the face labelled `C n`, where the label `B (n + 1)` is `0`, and the
last term `(1 + A n).val` of `potentialPhi n A`. -/
private lemma stripPotential_terminal (a b t t' c : ZMod 2) :
    2 * (1 + t).val + (1 + t').val ≤
      stripPotential a b t +
      ((1 + c + a + b).val + (1 + c + a + 0).val +
        (1 + c + b + t).val + (1 + c + 0 + t').val) +
      (1 + a).val := by
  decide +revert

/-- The energy of two qubits whose spins differ by `a + a'` is at least
`a + a'`. -/
private lemma pair_difference_le (a a' b s : ZMod 2) :
    (a + a').val ≤ (1 + s + a + b).val + (1 + s + a' + b).val := by
  decide +revert

/-- The sum of the first `n` middle steps of the sweep. -/
private lemma stripPotential_path (n : ℕ) (A B C s t : ℕ → ZMod 2) :
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

/-- The shell inequality: if the lower bound `potentialPhi n A` holds for the
apex and the first `n` layers, then `potentialPhi (n + 1) t` holds after
adding the layer with rows `A`, `B`, `C` of face labels, provided the label
`B (n + 1)` beyond the end of its row is `0`. -/
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

/-- When the next row of face labels is zero, the lower bound for the first `n`
layers is the distance `2 * n + 1`. -/
@[simp] lemma potentialPhi_zero (n : ℕ) :
    potentialPhi n (fun _ => 0) = 2 * n + 1 := by
  simp [potentialPhi, show (1 : ZMod 2).val = 1 from rfl]

end Quantum.StabilizerGroup.ColorCode

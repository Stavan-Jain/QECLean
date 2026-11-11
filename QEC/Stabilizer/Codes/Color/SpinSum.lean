import QEC.Stabilizer.Codes.Color.Spin
import QEC.Stabilizer.Codes.Color.Logicals
import QEC.Stabilizer.Codes.Color.Energy

/-!
# The energy of a spin configuration as a sum over layers

The weight of the chain `allOnes r + checkCombination incidence a` is the
number of qubits of spin `1` for the face labels `a`. Summing the spins over
the apex and the three rows of qubits of every layer expresses this weight as
`spinEnergy`, the energy of the apex plus the `shellEnergy` of the layers,
evaluated at the rows of labels `faceBit a 0`, `faceBit a 1` and `faceBit a 2`
(`chainWeight_allOnes_add_checkCombination_eq_spinEnergy`).

The steps are `chainWeight_eq_sum_val` (the weight of a chain is the sum of
its values), `sum_spinAt_eq_spinEnergy` (the sum over the qubits, layer by
layer) and `spinLayerEnergy_eq_shellEnergy` (the three rows of qubits of a
layer have energy `shellEnergy`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The energy of the patch of parameter `r` for the rows of face labels
`A l`, `B l`, `C l` of the layers `l`: the energy of the apex plus the
`shellEnergy` of the layers `l < r`. -/
def spinEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ) : ℕ :=
  (1 + A 0 0).val +
    ∑ l ∈ Finset.range r,
      shellEnergy (l + 1) (A l) (B l) (C l)
        (if l = 0 then fun _ => 0 else C (l - 1)) (A (l + 1))

/-- A sum over `2 * n` terms, grouped in consecutive pairs. -/
private lemma sum_range_even_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n), f j) =
      ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- A sum over `2 * n + 1` terms: the first term, and the others grouped in
consecutive pairs. -/
private lemma sum_range_odd_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1), f j) =
      f 0 + ∑ j ∈ Finset.range n, (f (2 * j + 1) + f (2 * j + 2)) := by
  rw [Finset.sum_range_succ', sum_range_even_pairs, add_comm]

/-- The energy of the three rows of qubits of layer `l`, as sums of the spins
at the coordinates `qubitCoord` of their qubits. -/
def spinLayerEnergy {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (2 * l + 1),
    (spinAt a (3 * l + 1, 3 * (j / 2) + 2 * (j % 2))).val) +
  (∑ j ∈ Finset.range (2 * (l + 1)),
    (spinAt a (3 * l + 2, 3 * (j / 2) + 1 + j % 2)).val) +
  (∑ j ∈ Finset.range (2 * (l + 1) + 1),
    (spinAt a (3 * l + 3, 3 * (j / 2) + j % 2)).val)

/-- The energy of the three rows of qubits of layer `l` is the `shellEnergy`
of the rows of face labels of the layers `l - 1`, `l` and `l + 1`. -/
lemma spinLayerEnergy_eq_shellEnergy {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) :
    spinLayerEnergy a l =
      shellEnergy (l + 1) (faceBit a 0 l) (faceBit a 1 l) (faceBit a 2 l)
        (if l = 0 then fun _ => 0 else faceBit a 2 (l - 1))
        (faceBit a 0 (l + 1)) := by
  have e1 (j : ℕ) : 3 * ((2 * j + 1) / 2) + 2 * ((2 * j + 1) % 2) = 3 * j + 2 := by omega
  have e2 (j : ℕ) : 3 * ((2 * j + 2) / 2) + 2 * ((2 * j + 2) % 2) = 3 * j + 3 := by omega
  have e3 (j : ℕ) : 3 * (2 * j / 2) + 1 + 2 * j % 2 = 3 * j + 1 := by omega
  have e4 (j : ℕ) : 3 * ((2 * j + 1) / 2) + 1 + (2 * j + 1) % 2 = 3 * j + 2 := by omega
  have e5 (j : ℕ) : 3 * ((2 * j + 1) / 2) + (2 * j + 1) % 2 = 3 * j + 1 := by omega
  have e6 (j : ℕ) : 3 * ((2 * j + 2) / 2) + (2 * j + 2) % 2 = 3 * j + 3 := by omega
  simp only [spinLayerEnergy, shellEnergy, fourBitCost, aPairCost, sum_range_odd_pairs,
    sum_range_even_pairs, e1, e2, e3, e4, e5, e6, Nat.zero_div, Nat.zero_mod, mul_zero, add_zero,
    spinAt_a0, spinAt_a_odd, spinAt_a_even_succ, spinAt_b_even, spinAt_b_odd, spinAt_c0,
    spinAt_c_odd, spinAt_c_even_succ, ite_apply, Nat.add_sub_cancel, Finset.sum_add_distrib]
  omega

/-- The weight of a chain is the sum of its values. -/
lemma chainWeight_eq_sum_val {r : ℕ} (c : Qubit r → ZMod 2) :
    (homologicalCode r).chainWeight c = ∑ q, (c q).val := by
  have h : ∀ z : ZMod 2, (if z ≠ 0 then 1 else 0) = z.val := by decide
  rw [HomologicalCode.chainWeight, HomologicalCode.chainSupport, Finset.card_filter]
  exact Finset.sum_congr rfl fun q _ => h (c q)

/-- The sum of the spins over all qubits is the energy of the apex plus the
`shellEnergy` of the layers. -/
lemma sum_spinAt_eq_spinEnergy {r : ℕ} (a : Face r → ZMod 2) :
    (∑ q : Qubit r, (spinAt a (qubitCoord q)).val) =
      spinEnergy (faceBit a 0) (faceBit a 1) (faceBit a 2) r := by
  have hlayer (l : Fin r) :
      (∑ k : Fin 3, ∑ j : Fin (2 * l.val + 1 + k.val),
        (spinAt a (qubitCoord (.inr ⟨l, k, j⟩))).val) =
        spinLayerEnergy a l.val := by
    rw [Fin.sum_univ_three]
    simpa [qubitCoord, spinLayerEnergy, Nat.add_assoc, Nat.mul_add] using
      congrArg₂ (· + ·)
      (Fin.sum_univ_eq_sum_range
        (fun j => (spinAt a (3 * l.val + 1, 3 * (j / 2) + 2 * (j % 2))).val)
        (2 * l.val + 1))
      (congrArg₂ (· + ·)
        (Fin.sum_univ_eq_sum_range
          (fun j => (spinAt a (3 * l.val + 2, 3 * (j / 2) + (1 + j % 2))).val)
          (2 * l.val + 2))
        (Fin.sum_univ_eq_sum_range
          (fun j => (spinAt a (3 * l.val + 3, 3 * (j / 2) + j % 2)).val)
          (2 * l.val + 3)))
  change (∑ q : Unit ⊕ LayerQubit r, (spinAt a (qubitCoord q)).val) = _
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, LayerQubit, Fintype.sum_sigma]
  change (spinAt a (0, 0)).val +
    (∑ l : Fin r, ∑ k : Fin 3, ∑ j : Fin (2 * l.val + 1 + k.val),
      (spinAt a (qubitCoord (.inr ⟨l, k, j⟩))).val) = _
  simp_rw [hlayer]
  rw [spinAt_apex, Fin.sum_univ_eq_sum_range]
  simp_rw [spinLayerEnergy_eq_shellEnergy]
  rfl

/-- The weight of the all-ones chain plus the combination of face checks with
coefficients `a` is the energy of the face labels `a`. -/
theorem chainWeight_allOnes_add_checkCombination_eq_spinEnergy {r : ℕ}
    (a : Face r → ZMod 2) :
    (homologicalCode r).chainWeight
        (allOnes r + SelfDual.checkCombination (@incidence r) a) =
      spinEnergy (faceBit a 0) (faceBit a 1) (faceBit a 2) r := by
  rw [chainWeight_eq_sum_val, ← sum_spinAt_eq_spinEnergy]
  exact Finset.sum_congr rfl fun q _ => congrArg ZMod.val (spinAt_qubitCoord a q).symm

end Quantum.StabilizerGroup.ColorCode

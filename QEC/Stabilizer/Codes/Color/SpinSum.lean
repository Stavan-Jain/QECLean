import QEC.Stabilizer.Codes.Color.Spin
import QEC.Stabilizer.Codes.Color.Logicals
import QEC.Stabilizer.Codes.Color.Energy

/-!
# Summing the triangular color-code spin energy

The explicit qubit enumeration partitions the Hamming weight into the apex
and its successive three-row shells. This file identifies that partition
with the energy used by the uniform distance certificate.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The total spin energy, expressed as the apex and its three-row shells. -/
def spinEnergy (A B C : ℕ → ℕ → ZMod 2) (r : ℕ) : ℕ :=
  (1 + A 0 0).val +
    ∑ l ∈ Finset.range r,
      shellEnergy (l + 1) (A l) (B l) (C l)
        (if l = 0 then fun _ => 0 else C (l - 1)) (A (l + 1))

/-- Split a row of even length into its consecutive pairs. -/
private theorem sum_range_even_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n), f j) =
      ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      omega

/-- Split a row of odd length into its first site and consecutive pairs. -/
private theorem sum_range_odd_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1), f j) =
      f 0 + ∑ j ∈ Finset.range n, (f (2 * j + 1) + f (2 * j + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      omega

/-- The energy of the three explicitly enumerated physical rows in one layer. -/
def spinLayerEnergy {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (2 * l + 1),
    (spinAt a (3 * l + 1, 3 * (j / 2) + 2 * (j % 2))).val) +
  (∑ j ∈ Finset.range (2 * (l + 1)),
    (spinAt a (3 * l + 2, 3 * (j / 2) + 1 + j % 2)).val) +
  (∑ j ∈ Finset.range (2 * (l + 1) + 1),
    (spinAt a (3 * l + 3, 3 * (j / 2) + j % 2)).val)

/-- The physical row enumeration gives exactly the shell energy. -/
theorem spinLayerEnergy_eq_shellEnergy {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) :
    spinLayerEnergy a l =
      shellEnergy (l + 1) (faceBit a 0 l) (faceBit a 1 l) (faceBit a 2 l)
        (if l = 0 then fun _ => 0 else faceBit a 2 (l - 1))
        (faceBit a 0 (l + 1)) := by
  have ha :
      (∑ j ∈ Finset.range (2 * l + 1),
        (spinAt a (3 * l + 1, 3 * (j / 2) + 2 * (j % 2))).val) =
      (1 + faceBit a 0 l 0 + faceBit a 1 l 0).val +
        ∑ j ∈ Finset.range l,
          aPairCost (faceBit a 0 l) (faceBit a 1 l)
            (if l = 0 then fun _ => 0 else faceBit a 2 (l - 1)) j := by
    rw [sum_range_odd_pairs]
    apply congrArg₂ (· + ·)
    · simpa using congrArg ZMod.val (spinAt_a0 a l)
    · apply Finset.sum_congr rfl
      intro j _
      have h1 : 3 * ((2 * j + 1) / 2) + 2 * ((2 * j + 1) % 2) =
          3 * j + 2 := by omega
      have h2 : 3 * ((2 * j + 2) / 2) + 2 * ((2 * j + 2) % 2) =
          3 * j + 3 := by omega
      rw [h1, h2, spinAt_a_odd, spinAt_a_even_succ]
      by_cases hl : l = 0 <;> simp [aPairCost, hl]
  have hb :
      (∑ j ∈ Finset.range (2 * (l + 1)),
        (spinAt a (3 * l + 2, 3 * (j / 2) + 1 + j % 2)).val) =
      ∑ j ∈ Finset.range (l + 1),
        ((1 + faceBit a 2 l j + faceBit a 0 l j + faceBit a 1 l j).val +
          (1 + faceBit a 2 l j + faceBit a 0 l j + faceBit a 1 l (j + 1)).val) := by
    rw [sum_range_even_pairs]
    apply Finset.sum_congr rfl
    intro j _
    have h0 : 3 * ((2 * j) / 2) + 1 + (2 * j) % 2 = 3 * j + 1 := by omega
    have h1 : 3 * ((2 * j + 1) / 2) + 1 + (2 * j + 1) % 2 = 3 * j + 2 := by omega
    rw [h0, h1, spinAt_b_even, spinAt_b_odd]
  have hc :
      (∑ j ∈ Finset.range (2 * (l + 1) + 1),
        (spinAt a (3 * l + 3, 3 * (j / 2) + j % 2)).val) =
      (1 + faceBit a 1 l 0 + faceBit a 0 (l + 1) 0).val +
        ∑ j ∈ Finset.range (l + 1),
          ((1 + faceBit a 2 l j + faceBit a 1 l j + faceBit a 0 (l + 1) j).val +
            (1 + faceBit a 2 l j + faceBit a 1 l (j + 1) +
              faceBit a 0 (l + 1) (j + 1)).val) := by
    rw [sum_range_odd_pairs]
    apply congrArg₂ (· + ·)
    · simpa using congrArg ZMod.val (spinAt_c0 a l)
    · apply Finset.sum_congr rfl
      intro j _
      have h1 : 3 * ((2 * j + 1) / 2) + (2 * j + 1) % 2 = 3 * j + 1 := by omega
      have h2 : 3 * ((2 * j + 2) / 2) + (2 * j + 2) % 2 = 3 * j + 3 := by omega
      rw [h1, h2, spinAt_c_odd, spinAt_c_even_succ]
  rw [spinLayerEnergy, ha, hb, hc]
  simp only [shellEnergy, Nat.add_sub_cancel, fourBitCost, Finset.sum_add_distrib]
  omega

/-- Binary Hamming weight equals the sum of the bit values. -/
theorem chainWeight_eq_sum_val {r : ℕ} (c : Qubit r → ZMod 2) :
    (homologicalCode r).chainWeight c = ∑ q, (c q).val := by
  classical
  simp only [HomologicalCode.chainWeight, HomologicalCode.chainSupport,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  have h : ∀ z : ZMod 2, (if z ≠ 0 then (1 : ℕ) else 0) = z.val := by decide
  exact h (c q)

/-- The finite qubit enumeration sums to the apex and all shell energies. -/
theorem sum_spinAt_eq_spinEnergy {r : ℕ} (a : Face r → ZMod 2) :
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

/-- An odd logical coset has exactly the spin energy of its face labels. -/
theorem chainWeight_allOnes_add_checkCombination_eq_spinEnergy {r : ℕ}
    (a : Face r → ZMod 2) :
    (homologicalCode r).chainWeight
        (allOnes r + SelfDual.checkCombination (@incidence r) a) =
      spinEnergy (faceBit a 0) (faceBit a 1) (faceBit a 2) r := by
  rw [chainWeight_eq_sum_val]
  calc
    (∑ q, ((allOnes r + SelfDual.checkCombination (@incidence r) a) q).val) =
        ∑ q, (spinAt a (qubitCoord q)).val := by
      apply Finset.sum_congr rfl
      intro q _
      rw [spinAt_qubitCoord]
      rfl
    _ = _ := sum_spinAt_eq_spinEnergy a

end Quantum.StabilizerGroup.ColorCode

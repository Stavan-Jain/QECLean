import QEC.Stabilizer.Framework.Homological.Distance
import Mathlib.InformationTheory.Hamming

/-!
# Weighted packing bounds for binary logical operators

If a binary vector pairs to one with each member of a representative family,
its support meets every representative. Natural multiplicities and a bound
on weighted overlap at each qubit give a lower bound on its Hamming weight.
Rational weights can be represented by clearing denominators.

For homological codes, representatives differing by opposite boundaries have
the same pairing on cycles. An explicit coverage hypothesis selects a
family for every nonboundary cycle. The module `LogicalCoverage` discharges
that hypothesis using paired witnesses and a dimension bound.

The strict threshold `(D - 1) * cap < ∑ i, w i` retains integer rounding.
Neither `D`, `cap`, nor individual weights require a positivity assumption.
An empty representative family cannot satisfy this strict threshold. If the
capacity is zero, positive total weight is incompatible with the pairing
and overlap hypotheses. The counting inequality itself permits both cases.

This formalizes known overlap/disjointness arguments. See Audoux--Couvreur,
*On tensor products of CSS codes*, Corollary 2.11, and Bostanci--Kubica,
*Finding the disjointness of stabilizer codes is NP-complete*, Theorem 5.
No novelty of the distance mathematics is claimed.
-/

namespace Quantum.Stabilizer.Homological

open Matrix Finset

variable {Q I : Type} [Fintype Q] [Fintype I]

/-- Weighted double counting, independent of the logical dimension. -/
theorem weighted_overlap_bound (x : Q → ZMod 2) (z : I → Q → ZMod 2)
    (w : I → ℕ) (cap : ℕ) (hpair : ∀ i, x ⬝ᵥ z i = 1)
    (hcap : ∀ q, (∑ i, if z i q ≠ 0 then w i else 0) ≤ cap) :
    (∑ i, w i) ≤ cap * hammingNorm x := by
  classical
  have hmeet (i : I) : ∃ q, x q ≠ 0 ∧ z i q ≠ 0 := by
    by_contra h
    push Not at h
    have hz : x ⬝ᵥ z i = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      by_cases hx : x q = 0
      · simp [hx]
      · simp [h q hx]
    rw [hpair i] at hz
    exact one_ne_zero hz
  have hrow (i : I) : w i ≤ ∑ q, if x q ≠ 0 ∧ z i q ≠ 0 then w i else 0 := by
    obtain ⟨q, hx, hz⟩ := hmeet i
    calc w i = (if x q ≠ 0 ∧ z i q ≠ 0 then w i else 0) := by simp [hx, hz]
      _ ≤ ∑ q, if x q ≠ 0 ∧ z i q ≠ 0 then w i else 0 :=
        Finset.single_le_sum
          (f := fun q => if x q ≠ 0 ∧ z i q ≠ 0 then w i else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  calc (∑ i, w i)
      ≤ ∑ i, ∑ q, if x q ≠ 0 ∧ z i q ≠ 0 then w i else 0 :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = ∑ q, ∑ i, if x q ≠ 0 ∧ z i q ≠ 0 then w i else 0 := Finset.sum_comm
    _ ≤ ∑ q, if x q ≠ 0 then cap else 0 := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hx : x q ≠ 0
      · simpa [hx] using hcap q
      · simp [hx]
    _ = cap * hammingNorm x := by
      rw [hammingNorm, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp

namespace HomologicalCode

variable (X : HomologicalCode)

/-- Pairing a cycle with a dual-boundary difference gives zero. -/
theorem pairing_eq_of_dual_boundary {x z z' : X.C1 → ZMod 2}
    (hx : x ∈ X.cycles) (hz : z' - z ∈ X.dualBoundaries) :
    x ⬝ᵥ z' = x ⬝ᵥ z := by
  obtain ⟨s, hs⟩ := hz
  have hx0 : X.boundary1 x = 0 := hx
  have hzero : x ⬝ᵥ X.cutMap s = 0 := by
    have h := X.boundary1_cutMap_transpose x s
    simpa [hx0, dotProduct] using h.symm
  rw [hs, dotProduct_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Pairing a dual cycle with a boundary difference gives zero. -/
theorem pairing_eq_of_boundary {x z z' : X.C1 → ZMod 2}
    (hx : x ∈ X.dualCycles) (hz : z' - z ∈ X.boundaries) :
    x ⬝ᵥ z' = x ⬝ᵥ z := by
  obtain ⟨f, hf⟩ := hz
  have hx0 : X.dualBoundary x = 0 := hx
  have hzero : x ⬝ᵥ X.boundary2 f = 0 := by
    rw [dotProduct_comm]
    change (∑ e, X.boundary2 f e * x e) = 0
    rw [X.boundary2_dualBoundary_transpose, hx0]
    simp
  rw [hf, dotProduct_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- The strict threshold retains the integer ceiling, including for zero cap. -/
theorem chain_weight_ge_of_overlap (x : X.C1 → ZMod 2)
    (z : I → X.C1 → ZMod 2) (w : I → ℕ) (cap D : ℕ)
    (hpair : ∀ i, x ⬝ᵥ z i = 1)
    (hcap : ∀ q, (∑ i, if z i q ≠ 0 then w i else 0) ≤ cap)
    (hthreshold : (D - 1) * cap < ∑ i, w i) : D ≤ X.chainWeight x := by
  have hcount := weighted_overlap_bound x z w cap hpair hcap
  change D ≤ hammingNorm x
  by_contra h
  have hw : hammingNorm x ≤ D - 1 := by omega
  have hh := Nat.mul_le_mul_left cap hw
  nlinarith

/-- Arbitrary-k X bound with explicit logical-class coverage. -/
theorem chain_weight_ge_of_detecting_families {A : Type}
    (base : A → X.C1 → ZMod 2) (reps : A → I → X.C1 → ZMod 2)
    (w : A → I → ℕ) (cap : A → ℕ) (D : ℕ)
    (hclass : ∀ a i, reps a i - base a ∈ X.dualBoundaries)
    (hcover : ∀ x, x ∈ X.cycles → x ∉ X.boundaries → ∃ a, x ⬝ᵥ base a = 1)
    (hcap : ∀ a q, (∑ i, if reps a i q ≠ 0 then w a i else 0) ≤ cap a)
    (hthreshold : ∀ a, (D - 1) * cap a < ∑ i, w a i) :
    ∀ x, x ∈ X.cycles → x ∉ X.boundaries → D ≤ X.chainWeight x := by
  intro x hx hb
  obtain ⟨a, ha⟩ := hcover x hx hb
  apply chain_weight_ge_of_overlap X x (reps a) (w a) (cap a) D
    (fun i => (pairing_eq_of_dual_boundary X hx (hclass a i)).trans ha)
    (hcap a) (hthreshold a)

/-- Arbitrary-k Z bound, with the symmetric coverage requirement. -/
theorem dual_chain_weight_ge_of_detecting_families {A : Type}
    (base : A → X.C1 → ZMod 2) (reps : A → I → X.C1 → ZMod 2)
    (w : A → I → ℕ) (cap : A → ℕ) (D : ℕ)
    (hclass : ∀ a i, reps a i - base a ∈ X.boundaries)
    (hcover : ∀ x, x ∈ X.dualCycles → x ∉ X.dualBoundaries → ∃ a, x ⬝ᵥ base a = 1)
    (hcap : ∀ a q, (∑ i, if reps a i q ≠ 0 then w a i else 0) ≤ cap a)
    (hthreshold : ∀ a, (D - 1) * cap a < ∑ i, w a i) :
    ∀ x, x ∈ X.dualCycles → x ∉ X.dualBoundaries → D ≤ X.chainWeight x := by
  intro x hx hb
  obtain ⟨a, ha⟩ := hcover x hx hb
  apply chain_weight_ge_of_overlap X x (reps a) (w a) (cap a) D
    (fun i => (pairing_eq_of_boundary X hx (hclass a i)).trans ha)
    (hcap a) (hthreshold a)

end HomologicalCode
end Quantum.Stabilizer.Homological

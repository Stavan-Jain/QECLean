import QEC.Stabilizer.Codes.Color.Logicals
import QEC.Stabilizer.Framework.Homological.SelfDualLogical

/-!
# Binary logical classes of the triangular color code

The independent face checks span the even cycles. Every odd cycle differs
from the all-ones chain by a face-check combination. Thus the distance
problem reduces to the minimum support of an odd cycle in the patch.

The linear-algebra argument applies to every self-orthogonal binary check
matrix with independent rows and one more column than twice its row count.
-/

open scoped BigOperators

namespace Quantum.StabilizerGroup.ColorCode

open Stabilizer.Homological

/-- The face-boundary space consists exactly of the even cycles. -/
theorem mem_boundaries_iff_cycle_even {r : ℕ} (c : Qubit r → ZMod 2) :
    c ∈ (homologicalCode r).boundaries ↔
      c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 0 := by
  exact SelfDual.mem_range_checkCombination_iff (@incidence r) incidence_orthogonal
    (checkCombination_injective r)
    (by rw [card_qubit, card_face]; exact (twice_numFaces r).symm) c

/-- Every color-code cycle is its parity times the all-ones chain plus
a face boundary. -/
theorem exists_boundary_add_parity {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles) :
    ∃ b : Qubit r → ZMod 2, b ∈ (homologicalCode r).boundaries ∧
      c = b + (∑ q, c q) • allOnes r := by
  obtain ⟨a, ha⟩ := SelfDual.exists_checkCombination_add_parity
    (@incidence r) incidence_orthogonal (checkCombination_injective r)
    (by rw [card_qubit, card_face]; exact (twice_numFaces r).symm) c hc
  exact ⟨SelfDual.checkCombination (@incidence r) a, ⟨a, rfl⟩, ha⟩

/-- A cycle represents the nonzero binary logical class exactly when
it has odd parity. -/
theorem cycle_not_mem_boundaries_iff_odd {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles) :
    c ∉ (homologicalCode r).boundaries ↔ ∑ q, c q = 1 := by
  rw [mem_boundaries_iff_cycle_even, and_iff_right hc]
  have hzmod : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide
  exact hzmod _

/-- The odd cycles form the all-ones coset of the face-boundary space. -/
theorem odd_cycle_iff_allOnes_add_boundary {r : ℕ} (c : Qubit r → ZMod 2) :
    (c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 1) ↔
      ∃ b : Qubit r → ZMod 2, b ∈ (homologicalCode r).boundaries ∧
        c = allOnes r + b := by
  constructor
  · rintro ⟨hc, hpar⟩
    obtain ⟨b, hb, heq⟩ := exists_boundary_add_parity c hc
    refine ⟨b, hb, ?_⟩
    simpa only [hpar, one_smul, add_comm] using heq
  · rintro ⟨b, hb, rfl⟩
    have hbpar := (mem_boundaries_iff_cycle_even b).mp hb
    refine ⟨Submodule.add_mem _ (allOnes_mem_cycles r) hbpar.1, ?_⟩
    rw [show (∑ q, (allOnes r + b) q) =
      (∑ q, allOnes r q) + ∑ q, b q from Finset.sum_add_distrib]
    rw [hbpar.2, add_zero]
    simpa only [HomologicalCode.chainInnerProduct, allOnes, mul_one]
      using allOnes_innerProduct r

/-- A pure X chain is a nontrivial logical operator exactly when it is
an odd cycle. -/
theorem chainXOperator_nontrivial_iff_odd_cycle {r : ℕ} (c : Qubit r → ZMod 2) :
    IsNontrivialLogicalOperator ((homologicalCode r).chainXOperator c)
        (homologicalCode r).homologicalStabilizerGroup ↔
      c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 1 := by
  rw [HomologicalCode.chainXOperator_isNontrivialLogical_iff (X := homologicalCode r)]
  exact and_congr_right fun hc => cycle_not_mem_boundaries_iff_odd c hc

/-- A pure Z chain is a nontrivial logical operator exactly when it is
an odd cycle. -/
theorem chainZOperator_nontrivial_iff_odd_cycle {r : ℕ} (c : Qubit r → ZMod 2) :
    IsNontrivialLogicalOperator ((homologicalCode r).chainZOperator c)
        (homologicalCode r).homologicalStabilizerGroup ↔
      c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 1 := by
  rw [HomologicalCode.chainZOperator_isNontrivialLogical_iff (X := homologicalCode r),
    dualCycles_eq_cycles, dualBoundaries_eq_boundaries]
  exact and_congr_right fun hc => cycle_not_mem_boundaries_iff_odd c hc

end Quantum.StabilizerGroup.ColorCode

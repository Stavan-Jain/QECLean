import QEC.Stabilizer.Codes.Color.Logicals
import QEC.Stabilizer.Framework.Homological.SelfDualLogical

/-!
# The logical class of the triangular color code over `ZMod 2`

The face checks are independent and mutually orthogonal, and there is one more
qubit than twice the number of faces. Hence the boundaries of
`homologicalCode r` are exactly the cycles of even parity
(`mem_boundaries_iff_cycle_even`), a cycle is not a boundary iff it has odd
parity (`cycle_not_mem_boundaries_iff_odd`), and the cycles of odd parity are
the chains `allOnes r + b` with `b` a boundary
(`odd_cycle_iff_allOnes_add_boundary`). The X-chain and Z-chain operators that
are nontrivial logical operators are those of the odd cycles
(`chainXOperator_nontrivial_iff_odd_cycle`,
`chainZOperator_nontrivial_iff_odd_cycle`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The boundaries are exactly the cycles of even parity. -/
theorem mem_boundaries_iff_cycle_even {r : ℕ} (c : Qubit r → ZMod 2) :
    c ∈ (homologicalCode r).boundaries ↔
      c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 0 :=
  SelfDual.mem_range_checkCombination_iff (@incidence r) incidence_orthogonal
    (checkCombination_injective r) (card_qubit_eq_two_mul_card_face_add_one r) c

/-- Every cycle is a boundary plus its parity times the all-ones chain. -/
lemma exists_boundary_add_parity {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles) :
    ∃ b : Qubit r → ZMod 2, b ∈ (homologicalCode r).boundaries ∧
      c = b + (∑ q, c q) • allOnes r := by
  obtain ⟨a, ha⟩ := SelfDual.exists_checkCombination_add_parity
    (@incidence r) incidence_orthogonal (checkCombination_injective r)
    (card_qubit_eq_two_mul_card_face_add_one r) c hc
  exact ⟨SelfDual.checkCombination (@incidence r) a, ⟨a, rfl⟩, ha⟩

/-- A cycle is not a boundary iff it has odd parity. -/
theorem cycle_not_mem_boundaries_iff_odd {r : ℕ} (c : Qubit r → ZMod 2)
    (hc : c ∈ (homologicalCode r).cycles) :
    c ∉ (homologicalCode r).boundaries ↔ ∑ q, c q = 1 := by
  rw [mem_boundaries_iff_cycle_even, and_iff_right hc]
  exact zmod2_ne_zero_iff

/-- The cycles of odd parity are the all-ones chain plus the boundaries. -/
theorem odd_cycle_iff_allOnes_add_boundary {r : ℕ} (c : Qubit r → ZMod 2) :
    (c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 1) ↔
      ∃ b : Qubit r → ZMod 2, b ∈ (homologicalCode r).boundaries ∧
        c = allOnes r + b := by
  constructor
  · rintro ⟨hc, hpar⟩
    obtain ⟨b, hb, heq⟩ := exists_boundary_add_parity c hc
    exact ⟨b, hb, by simpa only [hpar, one_smul, add_comm] using heq⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hbc, hbpar⟩ := (mem_boundaries_iff_cycle_even b).mp hb
    refine ⟨Submodule.add_mem _ (allOnes_mem_cycles r) hbc, ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, allOnes_sum_one, hbpar, add_zero]

/-- The X-chain operator of `c` is a nontrivial logical operator iff `c` is a
cycle of odd parity. -/
theorem chainXOperator_nontrivial_iff_odd_cycle {r : ℕ} (c : Qubit r → ZMod 2) :
    IsNontrivialLogicalOperator ((homologicalCode r).chainXOperator c)
        (homologicalCode r).homologicalStabilizerGroup ↔
      c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 1 := by
  rw [HomologicalCode.chainXOperator_isNontrivialLogical_iff (X := homologicalCode r)]
  exact and_congr_right fun hc => cycle_not_mem_boundaries_iff_odd c hc

/-- The Z-chain operator of `c` is a nontrivial logical operator iff `c` is a
cycle of odd parity. -/
theorem chainZOperator_nontrivial_iff_odd_cycle {r : ℕ} (c : Qubit r → ZMod 2) :
    IsNontrivialLogicalOperator ((homologicalCode r).chainZOperator c)
        (homologicalCode r).homologicalStabilizerGroup ↔
      c ∈ (homologicalCode r).cycles ∧ ∑ q, c q = 1 := by
  rw [HomologicalCode.chainZOperator_isNontrivialLogical_iff (X := homologicalCode r),
    dualCycles_eq_cycles, dualBoundaries_eq_boundaries]
  exact and_congr_right fun hc => cycle_not_mem_boundaries_iff_odd c hc

end Quantum.StabilizerGroup.ColorCode

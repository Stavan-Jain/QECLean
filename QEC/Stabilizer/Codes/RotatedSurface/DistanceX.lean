import QEC.Stabilizer.Codes.RotatedSurface.StabilizerCode

/-!
# X-distance of the rotated surface code

Every cycle of the rotated surface code that is not a boundary has weight at
least `L` (`chainWeight_ge_L_of_nontrivial`), and the logical X operator, the
X-string on the middle column, has weight exactly `L` (`logicalX_weight_eq_L`).

The bound is an instance of the line-parity bound
`Homological.card_le_card_support_of_fiber_parity`, which also gives the
Z-distance: if the boundaries have codimension one in the cycles, every
boundary has an even number of cells on every line and some cycle has an odd
number of cells on every line, then a cycle that is not a boundary has a cell
on every line.

Here the lines are the rows of the grid. A combination of X-checks has an even
number of qubits in every row (`sum_row_rscBoundary2`), the middle column
`middleColChain L` has one (`sum_row_middleColChain`), and the boundaries have
codimension one in the cycles (`rsc_finrank_cycles_eq_boundaries_add_one`).
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped Homology RotatedSurfaceChain
open NQubitPauliGroupElement Stabilizer.Homological Stabilizer.Lattice.RotatedSurface

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## The middle column -/

omit [Fact (Odd L)] in
/-- The middle column has exactly one qubit in every row. -/
lemma sum_row_middleColChain (y : Fin L) :
    ∑ v : VtxIdx L with v.2 = y, middleColChain L v = 1 := by
  rw [Finset.sum_eq_single_of_mem (midIdx L, y) (by simp)]
  · simp [middleColChain]
  · rintro ⟨a, b⟩ hv hne
    obtain rfl : b = y := by simpa using hv
    exact if_neg fun h => hne (Prod.ext (Fin.ext h) rfl)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- A boundary has an even number of qubits in every row. -/
lemma sum_row_eq_zero_of_mem_boundaries {c : VtxIdx L → ZMod 2} (hc : c ∈ B₁ L) (y : Fin L) :
    ∑ v : VtxIdx L with v.2 = y, c v = 0 := by
  obtain ⟨f, rfl⟩ := hc
  exact sum_row_rscBoundary2 L f y

omit [Fact (Odd L)] in
/-- The middle column is not a boundary: it has one qubit in every row, and a
boundary an even number. -/
theorem middleColChain_not_mem_boundaries : middleColChain L ∉ B₁ L := fun h =>
  one_ne_zero <| (sum_row_middleColChain L (midIdx L)).symm.trans
    (sum_row_eq_zero_of_mem_boundaries L h (midIdx L))

/-! ## The weight of a nontrivial cycle -/

/-- A cycle that is not a boundary has weight at least `L`: it has a qubit in
every row, by `card_le_card_support_of_fiber_parity` applied to the rows. -/
theorem chainWeight_ge_L_of_nontrivial {c : VtxIdx L → ZMod 2} (hc : c ∈ Z₁ L)
    (hcB : c ∉ B₁ L) : L ≤ (rotatedSurfaceHomologicalCode L).chainWeight c :=
  (Fintype.card_fin L).ge.trans <|
    card_le_card_support_of_fiber_parity (Prod.snd : VtxIdx L → Fin L)
      (rscBoundaries_le_rscCycles L) rsc_finrank_cycles_eq_boundaries_add_one.le
      (fun _ hb y => sum_row_eq_zero_of_mem_boundaries L hb y)
      (middleColChain_mem_cycles L) (sum_row_middleColChain L) hc hcB

/-! ## The logical X operator -/

/-- The logical X operator is a nontrivial logical operator of the homological
stabilizer group: the middle column is a cycle and not a boundary. -/
theorem logicalX_isNontrivialLogicalOperator :
    IsNontrivialLogicalOperator (logicalX L)
      (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
  (HomologicalCode.chainXOperator_isNontrivialLogical_iff _).2
    ⟨middleColChain_mem_cycles L, middleColChain_not_mem_boundaries L⟩

/-- The logical X operator has weight `L`: it acts on the `L` qubits of the
middle column. -/
theorem logicalX_weight_eq_L : weight (logicalX L) = L := by
  have h : (Finset.univ.filter fun v : VtxIdx L => middleColChain L v ≠ 0) =
      {midIdx L} ×ˢ Finset.univ := by
    ext ⟨a, b⟩
    simp [middleColChain, Fin.ext_iff, eq_comm]
  exact (HomologicalCode.weight_chainXOperator (X := rotatedSurfaceHomologicalCode L) _).trans
    ((congrArg Finset.card h).trans (by simp))

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum

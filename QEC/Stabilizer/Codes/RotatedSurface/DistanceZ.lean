import QEC.Stabilizer.Codes.RotatedSurface.DistanceX

/-!
# Z-distance of the rotated surface code

Every dual cycle of the rotated surface code that is not a dual boundary has
weight at least `L` (`dual_chainWeight_ge_L_of_nontrivial`), and the logical Z
operator, the Z-string on the middle row, has weight exactly `L`
(`logicalZ_weight_eq_L`).

This is the X-side argument with rows and columns exchanged, again through
`Homological.card_le_card_support_of_fiber_parity`: the lines are the columns
of the grid, a combination of Z-checks has an even number of qubits in every
column (`sum_col_rscZCutMap`), and the middle row `middleRowChain L` has one
(`sum_col_middleRowChain`). The dual boundaries have codimension one in the
dual cycles (`rsc_finrank_dualCycles_eq_dualBoundaries_add_one`) because, for
every `HomologicalCode`, the dual homology has the dimension of `H₁`
(`HomologicalCode.finrank_dualCycles_eq_dualBoundaries_add_H1`).
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace HomologicalCode

open scoped Homology

variable (X : HomologicalCode)

/-! ## The dimension of the dual homology -/

/-- `dualBoundary` and `∂₂` are transposes, so they have the same rank. -/
theorem finrank_range_dualBoundary :
    dim₂ (LinearMap.range X.dualBoundary) = dim₂ X.boundaries := by
  have hrank : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Finite B]
      (T : (A → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2)),
      dim₂ (LinearMap.range T) = (LinearMap.toMatrix' T).rank := fun {A B} _ _ _ T => by
    rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix' T) (Pi.basisFun (ZMod 2) B)
      (Pi.basisFun (ZMod 2) A), Matrix.toLin_eq_toLin', Matrix.toLin'_toMatrix']
  have h : LinearMap.toMatrix' X.dualBoundary =
      (LinearMap.toMatrix' X.boundary2).transpose := by
    ext f e
    simp [LinearMap.toMatrix'_apply, Pi.single_apply]
  rw [boundaries, hrank, hrank, h, Matrix.rank_transpose]

/-- The dual homology `dualCycles / dualBoundaries` has the dimension of `H₁`:
`dim dualCycles = dim dualBoundaries + dim H₁`. Both sides are
`dim C₁ - dim B₁`, as `dualCycles` is the kernel of the transpose of `∂₂` and
`dualBoundaries` the range of the transpose of `∂₁`. -/
theorem finrank_dualCycles_eq_dualBoundaries_add_H1 :
    dim₂ X.dualCycles = dim₂ X.dualBoundaries + dim₂ X.H1 := by
  have h1 := X.rank_nullity_boundary1
  have h2 : dim₂ X.dualBoundaries = dim₂ (LinearMap.range X.boundary1) :=
    X.finrank_range_cutMap
  have h3 : dim₂ (LinearMap.range X.dualBoundary) + dim₂ X.dualCycles =
      dim₂ (X.C1 → ZMod 2) := LinearMap.finrank_range_add_finrank_ker X.dualBoundary
  have h4 := X.finrank_range_dualBoundary
  have h5 := X.finrank_H1_eq_cycles_sub_boundaries
  have h6 := Submodule.finrank_mono X.boundaries_le_cycles
  omega

end HomologicalCode
end Homological
end Stabilizer

namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped Homology RotatedSurfaceChain
open NQubitPauliGroupElement Stabilizer.Homological Stabilizer.Lattice.RotatedSurface

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## The middle row -/

omit [Fact (Odd L)] in
/-- The middle row has exactly one qubit in every column. -/
lemma sum_col_middleRowChain (x : Fin L) :
    ∑ v : VtxIdx L with v.1 = x, middleRowChain L v = 1 := by
  rw [Finset.sum_eq_single_of_mem (x, midIdx L) (by simp)]
  · simp [middleRowChain]
  · rintro ⟨a, b⟩ hv hne
    obtain rfl : a = x := by simpa using hv
    exact if_neg fun h => hne (Prod.ext rfl (Fin.ext h))

/-- A dual boundary has an even number of qubits in every column. -/
lemma sum_col_eq_zero_of_mem_dualBoundaries {c : VtxIdx L → ZMod 2}
    (hc : c ∈ (rotatedSurfaceHomologicalCode L).dualBoundaries) (x : Fin L) :
    ∑ v : VtxIdx L with v.1 = x, c v = 0 := by
  obtain ⟨s, rfl⟩ := hc
  rw [rotatedSurfaceHomologicalCode_cutMap_eq]
  exact sum_col_rscZCutMap L s x

/-- The middle row is not a dual boundary: it has one qubit in every column,
and a dual boundary an even number. -/
theorem middleRowChain_not_mem_dualBoundaries :
    middleRowChain L ∉ (rotatedSurfaceHomologicalCode L).dualBoundaries := fun h =>
  one_ne_zero <| (sum_col_middleRowChain L (midIdx L)).symm.trans
    (sum_col_eq_zero_of_mem_dualBoundaries L h (midIdx L))

/-! ## The weight of a nontrivial dual cycle -/

/-- The dual boundaries have codimension one in the dual cycles. -/
theorem rsc_finrank_dualCycles_eq_dualBoundaries_add_one :
    dim₂ (rotatedSurfaceHomologicalCode L).dualCycles =
      dim₂ (rotatedSurfaceHomologicalCode L).dualBoundaries + 1 := by
  have h := (rotatedSurfaceHomologicalCode L).finrank_dualCycles_eq_dualBoundaries_add_H1
  rwa [show dim₂ (rotatedSurfaceHomologicalCode L).H1 = 1 from rsc_finrank_H1_eq_one] at h

/-- A dual cycle that is not a dual boundary has weight at least `L`: it has a
qubit in every column, by `card_le_card_support_of_fiber_parity` applied to the
columns. -/
theorem dual_chainWeight_ge_L_of_nontrivial {c : VtxIdx L → ZMod 2}
    (hc : c ∈ (rotatedSurfaceHomologicalCode L).dualCycles)
    (hcB : c ∉ (rotatedSurfaceHomologicalCode L).dualBoundaries) :
    L ≤ (rotatedSurfaceHomologicalCode L).chainWeight c :=
  (Fintype.card_fin L).ge.trans <|
    card_le_card_support_of_fiber_parity (Prod.fst : VtxIdx L → Fin L)
      (rotatedSurfaceHomologicalCode L).dualBoundaries_le_dualCycles
      (rsc_finrank_dualCycles_eq_dualBoundaries_add_one L).le
      (fun _ hb x => sum_col_eq_zero_of_mem_dualBoundaries L hb x)
      (middleRowChain_mem_dualCycles L) (sum_col_middleRowChain L) hc hcB

/-! ## The logical Z operator -/

/-- The logical Z operator is a nontrivial logical operator of the homological
stabilizer group: the middle row is a dual cycle and not a dual boundary. -/
theorem logicalZ_isNontrivialLogicalOperator :
    IsNontrivialLogicalOperator (logicalZ L)
      (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
  (HomologicalCode.chainZOperator_isNontrivialLogical_iff _).2
    ⟨middleRowChain_mem_dualCycles L, middleRowChain_not_mem_dualBoundaries L⟩

/-- The logical Z operator has weight `L`: it acts on the `L` qubits of the
middle row. -/
theorem logicalZ_weight_eq_L : weight (logicalZ L) = L := by
  have h : (Finset.univ.filter fun v : VtxIdx L => middleRowChain L v ≠ 0) =
      Finset.univ ×ˢ {midIdx L} := by
    ext ⟨a, b⟩
    simp [middleRowChain, Fin.ext_iff, eq_comm]
  exact (HomologicalCode.weight_chainZOperator (X := rotatedSurfaceHomologicalCode L) _).trans
    ((congrArg Finset.card h).trans (by simp))

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum

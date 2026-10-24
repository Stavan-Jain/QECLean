import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Packaging

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open HomologicalCode F2Mask
open scoped BigOperators

set_option maxRecDepth 200000
set_option exponentiation.threshold 400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The explicit weight 24 logical chain, read in reflected certificate
coordinates.
-/
noncomputable def witness24 : Group × Fin 2 → ZMod 2 := chainOfMask qubitEnum RankData.witness

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A dual chain separating the logical witness from all face boundaries. -/
noncomputable def witness24Dual : Group × Fin 2 → ZMod 2 := chainOfMask qubitEnum RankData.witnessDual

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The reflected first polynomial is the sum of its three reflected point masses.
-/
theorem reflectA_eq_singles : reflect A =
    Pi.single (-9,0) 1 + Pi.single (0,-1) 1 + Pi.single (0,-2) 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The reflected second polynomial is the sum of its three reflected point
masses.
-/
theorem reflectB_eq_singles : reflect B =
    Pi.single (0,-3) 1 + Pi.single (-25,0) 1 + Pi.single (-26,0) 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse evaluation of convolution by the first polynomial. -/
theorem convA_sparse (c : Group → ZMod 2) (g : Group) :
    (A ⋆ c) g = c (g - (9,0)) + c (g - (0,1)) + c (g - (0,2)) := by
  rw [A_eq_singles, conv_add_left, conv_add_left]
  simp only [Pi.add_apply, conv_single_left_apply]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Sparse evaluation of convolution by the second polynomial. -/
theorem convB_sparse (c : Group → ZMod 2) (g : Group) :
    (B ⋆ c) g = c (g - (0,3)) + c (g - (25,0)) + c (g - (26,0)) := by
  rw [B_eq_singles, conv_add_left, conv_add_left]
  simp only [Pi.add_apply, conv_single_left_apply]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The primal boundary uses only the six incident qubits. -/
theorem boundary1_sparse (c : Group × Fin 2 → ZMod 2) (g : Group) :
    complex.boundary1 c g =
      c (g - (0,3),0) + c (g - (25,0),0) + c (g - (26,0),0) +
      (c (g - (9,0),1) + c (g - (0,1),1) + c (g - (0,2),1)) := by
  change (B ⋆ leftHalf c) g + (A ⋆ rightHalf c) g = _
  rw [convB_sparse, convA_sparse]
  rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The dual boundary uses the six incident qubits with opposite shifts. -/
theorem dualBoundary_sparse (c : Group × Fin 2 → ZMod 2) (g : Group) :
    complex.dualBoundary c g =
      c (g - (-9,0),0) + c (g - (0,-1),0) + c (g - (0,-2),0) +
      (c (g - (0,-3),1) + c (g - (-25,0),1) + c (g - (-26,0),1)) := by
  change (bbChainComplex A B).dualBoundary c g = _
  rw [bb_dualBoundary_eq]
  rw [reflectA_eq_singles, reflectB_eq_singles,
    conv_add_left, conv_add_left, conv_add_left, conv_add_left]
  simp only [Pi.add_apply, conv_single_left_apply]
  rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The weight 24 witness satisfies every primal check. -/
theorem witness24_cycle : witness24 ∈ complex.cycles := by
  change complex.boundary1 witness24 = 0
  ext g
  rw [boundary1_sparse]
  have h : ∀ g : Group,
      witness24 (g - (0,3),0) + witness24 (g - (25,0),0) + witness24 (g - (26,0),0) +
      (witness24 (g - (9,0),1) + witness24 (g - (0,1),1) + witness24 (g - (0,2),1)) = 0 := by
    decide +kernel
  exact h g

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The separating witness annihilates every face boundary. -/
theorem witness24Dual_cycle : complex.dualBoundary witness24Dual = 0 := by
  ext g
  rw [dualBoundary_sparse]
  have h : ∀ g : Group,
      witness24Dual (g - (-9,0),0) + witness24Dual (g - (0,-1),0) + witness24Dual (g - (0,-2),0) +
      (witness24Dual (g - (0,-3),1) + witness24Dual (g - (-25,0),1) + witness24Dual (g - (-26,0),1)) = 0 := by
    decide +kernel
  exact h g

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The primal and separating witnesses have odd intersection. -/
theorem witness24_pairing : ∑ q : Group × Fin 2, witness24Dual q * witness24 q = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The explicit cycle is not a stabilizer boundary. -/
theorem witness24_not_boundary : witness24 ∉ complex.boundaries :=
  not_mem_boundaries_of_dual_witness witness24Dual_cycle witness24_pairing

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The explicit nontrivial cycle has weight 24. -/
theorem witness24_weight : complex.chainWeight witness24 = 24 := by
  change (Finset.univ.filter fun q => witness24 q ≠ 0).card = 24
  rw [card_support_eq_bitCount qubitEnum, witness24,
    maskOf_chainOfMask qubitEnum (by decide : RankData.witness < 2 ^ 360)]
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The code distance is 24 once the light-cycle exclusion is established. -/
theorem hasDistance24
    (lowerBound : ∀ c ∈ complex.cycles, c ∉ complex.boundaries →
      24 ≤ complex.chainWeight c) :
    Quantum.StabilizerGroup.HasCodeDistance stabilizerCode 24 := by
  have hdual := (bb_cycle_bound_iff_dual_bound A B 24).mp lowerBound
  refine Quantum.StabilizerGroup.hasCodeDistance_of stabilizerCode 24 (by decide) ?_ ?_
  · refine ⟨complex.chainXOperator witness24, ?_, ?_⟩
    · apply (Quantum.StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq
        _ stabilizerCode_subgroup).mpr
      exact (complex.chainXOperator_isNontrivialLogical_iff witness24).mpr
        ⟨witness24_cycle, witness24_not_boundary⟩
    · exact (weight_chainXOperator (X := complex) witness24).trans witness24_weight
  · intro w hw hd g hg hn
    have hc := (Quantum.StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq
      g stabilizerCode_subgroup).mp hn
    have hb := chainWeight_lower_bound_transfers complex 24 lowerBound hdual g hc
    change 24 ≤ Quantum.NQubitPauliGroupElement.weight g at hb
    omega

end Quantum.Stabilizer.Homological.BB.Bravyi360

#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.witness24_not_boundary
#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.hasDistance24

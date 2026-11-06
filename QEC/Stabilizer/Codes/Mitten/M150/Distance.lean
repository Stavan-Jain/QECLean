import QEC.Stabilizer.Codes.Mitten.M150.StabilizerCode
import QEC.Stabilizer.Codes.Mitten.M150.Witness
import QEC.Stabilizer.Codes.Mitten.M150.FloorXSide
import QEC.Stabilizer.Codes.Mitten.M150.FloorZSide
import QEC.Stabilizer.Codes.Mitten.M150.FloorSweepX
import QEC.Stabilizer.Codes.Mitten.M150.FloorSweepZ

/-!
# Distance ten for the `[[150,30]]` mitten code

The two chain-weight floors transfer through the generic homological CSS
bridge to a lower bound on every nontrivial logical operator. The explicit
weight-ten witness supplies the matching upper bound.

The four kernel-checked classification sweeps discharge both floor
certificates. The resulting `mitten150StabilizerCodeWithDistance` carries
all three parameters `[[150,30,10]]` in its type.
-/

namespace Quantum.Stabilizer.Homological.LP.M150

open Quantum.StabilizerGroup NQubitPauliGroupElement

/-- The two chain floors imply the lower bound on nontrivial logical weight. -/
theorem m150_logical_weight_ge_10_of_floors
    (hX : ∀ c : m150Complex.C1 → ZMod 2,
      m150Complex.boundary1 c = 0 → m150Complex.chainWeight c ≤ 9 →
        c ∈ m150Complex.boundaries)
    (hZ : ∀ c : m150Complex.C1 → ZMod 2,
      m150Complex.dualBoundary c = 0 → m150Complex.chainWeight c ≤ 9 →
        c ∈ m150Complex.dualBoundaries)
    (g : NQubitPauliGroupElement m150Complex.numQubits)
    (hg : IsNontrivialLogicalOperator g m150Complex.homologicalStabilizerGroup) :
    10 ≤ NQubitPauliGroupElement.weight g := by
  have floorX_contra : ∀ c ∈ m150Complex.cycles,
      c ∉ m150Complex.boundaries → 10 ≤ m150Complex.chainWeight c := by
    intro c hc hnb
    by_contra hlt
    push Not at hlt
    exact hnb (hX c ((m150Complex.mem_cycles_iff c).mp hc) (by omega))
  have floorZ_contra : ∀ c ∈ m150Complex.dualCycles,
      c ∉ m150Complex.dualBoundaries → 10 ≤ m150Complex.chainWeight c := by
    intro c hc hnb
    by_contra hlt
    push Not at hlt
    exact hnb (hZ c (LinearMap.mem_ker.mp hc) (by omega))
  exact HomologicalCode.chainWeight_lower_bound_transfers m150Complex 10
    floorX_contra floorZ_contra g hg

/-- The chain floors and the explicit witness establish distance exactly ten. -/
theorem m150StabilizerCode_hasCodeDistance_10_of_floors
    (hX : ∀ c : m150Complex.C1 → ZMod 2,
      m150Complex.boundary1 c = 0 → m150Complex.chainWeight c ≤ 9 →
        c ∈ m150Complex.boundaries)
    (hZ : ∀ c : m150Complex.C1 → ZMod 2,
      m150Complex.dualBoundary c = 0 → m150Complex.chainWeight c ≤ 9 →
        c ∈ m150Complex.dualBoundaries) :
    HasCodeDistance m150StabilizerCode 10 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro g hg _
    exact m150_logical_weight_ge_10_of_floors hX hZ g
      ((IsNontrivialLogicalOperator_of_toSubgroup_eq g
        m150StabilizerCode_toSubgroup_eq).mp hg)
  · refine ⟨m150Complex.chainZOperator witChain, ?_, ?_⟩
    · refine (IsNontrivialLogicalOperator_of_toSubgroup_eq _
        m150StabilizerCode_toSubgroup_eq).mpr ?_
      rw [HomologicalCode.chainZOperator_isNontrivialLogical_iff]
      exact ⟨LinearMap.mem_ker.mpr witChain_dualBoundary,
        witChain_not_mem_dualBoundaries⟩
    · rw [HomologicalCode.weight_chainZOperator]
      exact chainWeight_witChain

/-- Every cycle of weight at most nine is a boundary. -/
theorem floorX (c : m150Complex.C1 → ZMod 2)
    (hker : m150Complex.boundary1 c = 0)
    (hw : m150Complex.chainWeight c ≤ 9) :
    c ∈ m150Complex.boundaries :=
  floorX_of_certificates checkAll_Z0 checkAll_Z1 c hker hw

/-- Every dual cycle of weight at most nine is a dual boundary. -/
theorem floorZ (c : m150Complex.C1 → ZMod 2)
    (hker : m150Complex.dualBoundary c = 0)
    (hw : m150Complex.chainWeight c ≤ 9) :
    c ∈ m150Complex.dualBoundaries :=
  floorZ_of_certificates checkAll_X0 checkAll_X1 c hker hw

/-- Every nontrivial logical operator of the mitten complex has weight at least ten. -/
theorem m150_logical_weight_ge_10
    (g : NQubitPauliGroupElement m150Complex.numQubits)
    (hg : IsNontrivialLogicalOperator g m150Complex.homologicalStabilizerGroup) :
    10 ≤ NQubitPauliGroupElement.weight g :=
  m150_logical_weight_ge_10_of_floors floorX floorZ g hg

/-- The canonical mitten stabilizer code has distance exactly ten. -/
theorem m150StabilizerCode_hasCodeDistance_10 :
    HasCodeDistance m150StabilizerCode 10 :=
  m150StabilizerCode_hasCodeDistance_10_of_floors floorX floorZ

/-- The non-abelian lifted product over `C₅ × S₃` as a `[[150,30,10]]` code. -/
noncomputable def mitten150StabilizerCodeWithDistance :
    StabilizerCodeWithDistance 150 30 10 where
  toStabilizerCode := m150StabilizerCode
  hasDistance := m150StabilizerCode_hasCodeDistance_10

end Quantum.Stabilizer.Homological.LP.M150

#print axioms Quantum.Stabilizer.Homological.LP.M150.m150StabilizerCode_hasCodeDistance_10
#print axioms Quantum.Stabilizer.Homological.LP.M150.mitten150StabilizerCodeWithDistance

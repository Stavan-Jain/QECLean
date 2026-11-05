import QEC.Stabilizer.Framework.Homological.LogicalCoverage
import QEC.Stabilizer.Framework.Homological.SelfDual

/-!
# A homological packing proof for the four-qubit code

The single binary check `1111` gives X and Z stabilizers `XXXX` and `ZZZZ`.
Two paired witnesses certify all logical classes. Each detector has two
complementary representatives, with nonuniform weights 1 and 2 and capacity
2. The strict threshold `2 < 3` proves both chain-weight bounds of 2,
retaining the ceiling of `3 / 2`. The existing CSS bridge then bounds every
nontrivial Pauli logical. This is a separate example, independent of the
existing generator-presentation proof in `FourQubit_4_2_2`.
-/

namespace Quantum.Stabilizer.Homological.FourQubitPacking

open Matrix Module HomologicalCode

/-- One check acting on all four physical qubits. -/
def check : Fin 1 → Fin 4 → ZMod 2 := fun _ _ => 1

private theorem check_orthogonal : ∀ f g, ∑ q, check f q * check g q = 0 := by
  decide +kernel

/-- The self-dual chain complex with checks `XXXX` and `ZZZZ`. -/
def code : HomologicalCode :=
  SelfDual.homologicalCode check check_orthogonal 4 rfl (Equiv.refl _)

/-- Two independent logical detectors. -/
def detectors : Fin 2 → Fin 4 → ZMod 2 :=
  ![![0, 1, 0, 1], ![0, 0, 1, 1]]

/-- Logical cycles paired with the detectors by the identity matrix. -/
def witnesses : Fin 2 → Fin 4 → ZMod 2 :=
  ![![1, 1, 0, 0], ![1, 0, 1, 0]]

private theorem witness_mem : ∀ i, witnesses i ∈ code.cycles := by
  change ∀ i, SelfDual.syndrome check (witnesses i) = 0
  decide +kernel

private theorem paired : ∀ i j,
    witnesses i ⬝ᵥ detectors j = if i = j then 1 else 0 := by
  decide +kernel

private theorem detector_cycles : ∀ i, detectors i ∈ code.dualCycles := by
  rw [show code.dualCycles = code.cycles from SelfDual.dualCycles_eq_cycles ..]
  change ∀ i, SelfDual.syndrome check (detectors i) = 0
  decide +kernel

private theorem dimensions : finrank (ZMod 2) code.cycles = 3 ∧
    finrank (ZMod 2) code.boundaries = 1 := by
  have hsurj : Function.Surjective code.boundary1 := by
    change Function.Surjective (SelfDual.syndrome check)
    intro a
    refine ⟨![a 0, 0, 0, 0], ?_⟩
    ext v
    fin_cases v
    simp [SelfDual.syndrome, check, Fin.sum_univ_succ]
  have hinj : Function.Injective code.boundary2 := by
    change Function.Injective (SelfDual.checkCombination check)
    intro a b h
    ext f
    fin_cases f
    have h0 := congrFun h 0
    simpa [code, SelfDual.homologicalCode, SelfDual.checkCombination, check] using h0
  have hb : finrank (ZMod 2) code.boundaries = 1 := by
    exact (LinearMap.finrank_range_of_inj hinj).trans (Module.finrank_fin_fun ..)
  have hr := LinearMap.finrank_range_add_finrank_ker code.boundary1
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  change finrank (ZMod 2) (Fin 1 → ZMod 2) + finrank (ZMod 2) code.cycles =
    finrank (ZMod 2) (Fin 4 → ZMod 2) at hr
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hr
  omega

/-- Two-coordinate coverage of the entire primal logical quotient. -/
def coverage : CoverageCertificate code.cycles code.boundaries 2 where
  boundary_le := code.boundaries_le_cycles
  detectors := detectors
  witnesses := witnesses
  witness_mem := witness_mem
  boundary_zero := fun _ hb j => code.boundary_pairs_zero hb (detector_cycles j)
  paired := paired
  dimension_bound := by rw [dimensions.1, dimensions.2]

/-- Dual coverage uses the same paired vectors, by self-duality. -/
def dualCoverage : CoverageCertificate code.dualCycles code.dualBoundaries 2 where
  boundary_le := code.dual_boundaries_le_dual_cycles
  detectors := detectors
  witnesses := witnesses
  witness_mem := by
    rw [show code.dualCycles = code.cycles from SelfDual.dualCycles_eq_cycles ..]
    exact witness_mem
  boundary_zero := by
    rw [show code.dualBoundaries = code.boundaries from
      SelfDual.dualBoundaries_eq_boundaries ..]
    exact coverage.boundary_zero
  paired := paired
  dimension_bound := by
    rw [show code.dualCycles = code.cycles from SelfDual.dualCycles_eq_cycles ..,
      show code.dualBoundaries = code.boundaries from
        SelfDual.dualBoundaries_eq_boundaries .., dimensions.1, dimensions.2]

/-- There are two encoded qubits. -/
theorem homology_dimension : finrank (ZMod 2) code.H1 = 2 := by
  rw [code.finrank_H1_eq_cycles_sub_boundaries, dimensions.1, dimensions.2]

/-- A detector and its complement represent the same dual logical class. -/
def representatives (a i : Fin 2) : Fin 4 → ZMod 2 :=
  if i = 0 then detectors a else fun q => detectors a q + 1

/-- Nonuniform natural multiplicities: the two representatives have weights
1 and 2. -/
def weights : Fin 2 → ℕ := ![1, 2]

private theorem representative_class : ∀ a i,
    representatives a i - detectors a ∈ code.boundaries := by
  intro a i
  refine ⟨fun _ => if i = 0 then 0 else 1, ?_⟩
  fin_cases a <;> fin_cases i <;> decide +kernel

private theorem capacity : ∀ a q,
    (∑ i, if representatives a i q ≠ 0 then weights i else 0) ≤ 2 := by
  decide +kernel

/-- The weighted threshold retains the ceiling: floor division would give 1. -/
theorem weighted_threshold : (2 - 1) * 2 < ∑ i, weights i ∧
    (∑ i, weights i) / 2 = 1 := by
  decide +kernel

/-- Every nonboundary cycle has at least two physical qubits. -/
theorem chain_weight_ge : ∀ x ∈ code.cycles,
    x ∉ code.boundaries → 2 ≤ code.chainWeight x := by
  apply code.chain_weight_ge_of_certificate coverage representatives (fun _ => weights)
    (fun _ => 2) 2
  · change ∀ a i, representatives a i - detectors a ∈ code.dualBoundaries
    rw [show code.dualBoundaries = code.boundaries from
      SelfDual.dualBoundaries_eq_boundaries ..]
    exact representative_class
  · exact capacity
  · exact fun _ => weighted_threshold.1

/-- The same packing argument bounds every nonboundary dual cycle. -/
theorem dual_chain_weight_ge : ∀ x ∈ code.dualCycles,
    x ∉ code.dualBoundaries → 2 ≤ code.chainWeight x := by
  apply code.dual_chain_weight_ge_of_certificate dualCoverage representatives (fun _ => weights)
    (fun _ => 2) 2
  · change ∀ a i, representatives a i - detectors a ∈ code.boundaries
    exact representative_class
  · exact capacity
  · exact fun _ => weighted_threshold.1

/-- The upstream CSS bridge gives a Pauli-weight lower bound of two. -/
theorem pauli_weight_ge (g : NQubitPauliGroupElement 4)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g code.homologicalStabilizerGroup) :
    2 ≤ NQubitPauliGroupElement.weight g :=
  code.chainWeight_lower_bound_transfers 2 chain_weight_ge dual_chain_weight_ge g hg

/-- A weight-two Pauli logical attains the bound. -/
theorem weight_two_logical : ∃ g : NQubitPauliGroupElement 4,
    StabilizerGroup.IsNontrivialLogicalOperator g code.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 2 := by
  refine ⟨code.chainXOperator (witnesses 0), ?_, ?_⟩
  · apply (code.chainXOperator_isNontrivialLogical_iff _).mpr
    refine ⟨witness_mem 0, ?_⟩
    intro hb
    have hz := coverage.boundary_zero _ hb 0
    have hp := paired 0 0
    change witnesses 0 ⬝ᵥ detectors 0 = 0 at hz
    rw [if_pos rfl, hz] at hp
    exact zero_ne_one hp
  · calc
      _ = code.chainWeight (witnesses 0) := weight_chainXOperator _
      _ = 2 := by decide +kernel

end Quantum.Stabilizer.Homological.FourQubitPacking

import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Packaging a homological code as a stabilizer code

An independent pair of chain lists spanning the boundaries and coboundaries
specifies the independent CSS generators. The construction below derives the
stabilizer conditions and identifies the resulting subgroup with the canonical
homological stabilizer group. Chain distance bounds and a tight cycle then give
a `StabilizerCodeWithDistance` without further Pauli calculations.
-/

namespace Quantum.Stabilizer.Homological.HomologicalCode

open Quantum.StabilizerGroup
open NQubitPauliGroupElement

variable (X : HomologicalCode)

/-- The CSS generator list associated with chosen X- and Z-chain lists. -/
noncomputable def chainGeneratorsList
    (xChains zChains : List (X.C1 → ZMod 2)) :
    List (NQubitPauliGroupElement X.numQubits) :=
  xChains.map X.chainXOperator ++ zChains.map X.chainZOperator

/-- Linear algebra certificates for an independent CSS presentation.

The two span equalities express completeness of the chosen chain lists.
Independence is stated using the existing check-matrix API, and the length
certificate fixes the number of encoded qubits.
-/
structure CSSGeneratorPresentation (k : ℕ) where
  /-- Chosen chains for the X-type stabilizer generators. -/
  xChains : List (X.C1 → ZMod 2)
  /-- Chosen chains for the Z-type stabilizer generators. -/
  zChains : List (X.C1 → ZMod 2)
  /-- The chosen X-chains span all boundaries. -/
  x_span : Submodule.span (ZMod 2) {c | c ∈ xChains} = X.boundaries
  /-- The chosen Z-chains span all coboundaries. -/
  z_span : Submodule.span (ZMod 2) {c | c ∈ zChains} = X.dualBoundaries
  /-- The check-matrix rows of the combined CSS list are independent. -/
  independent : rowsLinearIndependent (X.chainGeneratorsList xChains zChains)
  /-- The logical-qubit count does not exceed the physical-qubit count. -/
  hk : k ≤ X.numQubits
  /-- The number of independent generators is the required `n - k`. -/
  length_eq : xChains.length + zChains.length = X.numQubits - k

variable {X}

/-- An additive binary-chain operator sends a linear span into the subgroup
closure of the corresponding operators. -/
private theorem operator_mem_closure_of_mem_span
    {V G : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Group G]
    (op : V → G) (hzero : op 0 = 1)
    (hadd : ∀ a b, op (a + b) = op a * op b)
    (s : Set V) {v : V} (hv : v ∈ Submodule.span (ZMod 2) s) :
    op v ∈ Subgroup.closure (op '' s) := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Subgroup.subset_closure ⟨v, hv, rfl⟩
  | zero => rw [hzero]; exact (Subgroup.closure _).one_mem
  | add a b _ _ ha hb => rw [hadd]; exact (Subgroup.closure _).mul_mem ha hb
  | smul a v _ hv =>
    have ha : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases ha a with rfl | rfl
    · simpa only [zero_smul, hzero] using (Subgroup.closure (op '' s)).one_mem
    · simpa only [one_smul] using hv

namespace CSSGeneratorPresentation

variable {k : ℕ} (D : X.CSSGeneratorPresentation k)

/-- Every chosen X-chain is a boundary. -/
theorem xChain_mem_boundaries {c : X.C1 → ZMod 2} (hc : c ∈ D.xChains) :
    c ∈ X.boundaries := by
  rw [← D.x_span]
  exact Submodule.subset_span hc

/-- Every chosen Z-chain is a coboundary. -/
theorem zChain_mem_dualBoundaries {c : X.C1 → ZMod 2} (hc : c ∈ D.zChains) :
    c ∈ X.dualBoundaries := by
  rw [← D.z_span]
  exact Submodule.subset_span hc

/-- Each selected CSS generator belongs to the canonical stabilizer subgroup. -/
theorem generator_mem_homologicalStabilizerGroup
    {g : NQubitPauliGroupElement X.numQubits}
    (hg : g ∈ X.chainGeneratorsList D.xChains D.zChains) :
    g ∈ X.homologicalStabilizerGroup.toSubgroup := by
  rcases List.mem_append.mp hg with hx | hz
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.closure_mono XGenerators_subset_homologicalGenerators
      ((chainXOperator_mem_XClosure_iff_mem_boundaries c).mpr
        (D.xChain_mem_boundaries hc))
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact Subgroup.closure_mono ZGenerators_subset_homologicalGenerators
      (chainZOperator_mem_ZClosure_of_mem_dualBoundaries c
        (D.zChain_mem_dualBoundaries hc))

/-- The selected generators span the full canonical stabilizer subgroup. -/
theorem closure_chainGeneratorsList_eq :
    Subgroup.closure (listToSet (X.chainGeneratorsList D.xChains D.zChains)) =
      X.homologicalStabilizerGroup.toSubgroup := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun g hg => D.generator_mem_homologicalStabilizerGroup hg
  · apply (Subgroup.closure_le _).mpr
    rintro g (hg | hg)
    · obtain ⟨v, rfl⟩ := hg
      have hc : X.cutMap (X.singleVtx v) ∈
          Submodule.span (ZMod 2) {c | c ∈ D.zChains} := by
        rw [D.z_span]
        exact ⟨X.singleVtx v, rfl⟩
      have hp := operator_mem_closure_of_mem_span X.chainZOperator
        chainZOperator_zero chainZOperator_add _ hc
      apply Subgroup.closure_mono _ hp
      rintro _ ⟨c, hc, rfl⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    · obtain ⟨f, rfl⟩ := hg
      have hc : X.boundary2 (X.singleFace f) ∈
          Submodule.span (ZMod 2) {c | c ∈ D.xChains} := by
        rw [D.x_span]
        exact ⟨X.singleFace f, rfl⟩
      have hp := operator_mem_closure_of_mem_span X.chainXOperator
        chainXOperator_zero chainXOperator_add _ hc
      apply Subgroup.closure_mono _ hp
      rintro _ ⟨c, hc, rfl⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- An independent CSS presentation packages the homological stabilizer code. -/
noncomputable def toStabilizerCode : StabilizerCode X.numQubits k where
  hk := D.hk
  generatorsList := X.chainGeneratorsList D.xChains D.zChains
  generators_length := by simpa only [chainGeneratorsList, List.length_append,
    List.length_map] using D.length_eq
  generators_phaseZero := by
    intro g hg
    rcases List.mem_append.mp hg with hx | hz
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      exact (chainXOperator_isXType c).1
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hz
      exact (chainZOperator_isZType c).1
  generators_independent := rowsLinearIndependent_implies_independentGenerators _ D.independent
  generators_commute := fun g hg h hh =>
    X.homologicalStabilizerGroup.is_abelian g h
      (D.generator_mem_homologicalStabilizerGroup hg)
      (D.generator_mem_homologicalStabilizerGroup hh)
  closure_no_neg_identity := by
    rw [D.closure_chainGeneratorsList_eq]
    exact X.homologicalStabilizerGroup.no_neg_identity

/-- The packaged stabilizer subgroup equals the canonical homological one. -/
theorem toStabilizerCode_toSubgroup_eq :
    D.toStabilizerCode.toStabilizerGroup.toSubgroup =
      X.homologicalStabilizerGroup.toSubgroup :=
  D.closure_chainGeneratorsList_eq

/-- Nontrivial logical operators are unchanged by the independent presentation. -/
theorem isNontrivialLogicalOperator_iff (g : NQubitPauliGroupElement X.numQubits) :
    IsNontrivialLogicalOperator g D.toStabilizerCode.toStabilizerGroup ↔
      IsNontrivialLogicalOperator g X.homologicalStabilizerGroup :=
  IsNontrivialLogicalOperator_of_toSubgroup_eq g D.toStabilizerCode_toSubgroup_eq

/-- Bounds on both chain sectors and an attaining X-cycle prove exact distance. -/
theorem hasCodeDistance_of_chain_bounds {d : ℕ} (hd : 1 ≤ d)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → d ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → d ≤ X.chainWeight c)
    (c : X.C1 → ZMod 2) (hc : c ∈ X.cycles) (hnb : c ∉ X.boundaries)
    (hw : X.chainWeight c = d) :
    HasCodeDistance D.toStabilizerCode d := by
  refine ⟨hd, ?_, X.chainXOperator c, ?_, ?_⟩
  · intro g hg _
    exact chainWeight_lower_bound_transfers X d hX hZ g
      ((D.isNontrivialLogicalOperator_iff g).mp hg)
  · exact (D.isNontrivialLogicalOperator_iff _).mpr
      ((chainXOperator_isNontrivialLogical_iff c).mpr ⟨hc, hnb⟩)
  · simpa only [weight_chainXOperator] using hw

/-- Package an independent homological CSS presentation with exact distance. -/
noncomputable def toStabilizerCodeWithDistance {d : ℕ} (hd : 1 ≤ d)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → d ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → d ≤ X.chainWeight c)
    (c : X.C1 → ZMod 2) (hc : c ∈ X.cycles) (hnb : c ∉ X.boundaries)
    (hw : X.chainWeight c = d) :
    StabilizerCodeWithDistance X.numQubits k d where
  toStabilizerCode := D.toStabilizerCode
  hasDistance := D.hasCodeDistance_of_chain_bounds hd hX hZ c hc hnb hw

end CSSGeneratorPresentation
end Quantum.Stabilizer.Homological.HomologicalCode

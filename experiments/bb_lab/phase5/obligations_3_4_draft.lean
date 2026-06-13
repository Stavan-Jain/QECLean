-- Phase 5 obligations 3+4 DRAFT (structurally correct, needs whnf perf tuning).
-- Append into StabilizerCode.lean §6. Issues: centralizer rw + commute_or_anticommute
-- whnf-timeout on the noncomputable grossComplex + 132-element-literal defeq.
-- TODO: avoid whnf — e.g. anticommute via anticommutes_iff_odd_anticommutes + the
-- inner-product count (no commute_or_anticommute compute); centralizer via a
-- subgroup-eq membership lemma that doesn't reduce packagedSG.toSubgroup; consider
-- attribute [irreducible] on the literal lists scoped to §6.

/-! ## §6  Packaged stabilizer group, logical operators, the StabilizerCode + HasCodeDistance -/

lemma listToSet_packaged_subset_homGens :
    listToSet genListPackaged ⊆ grossComplex.homologicalGenerators := by
  intro g hg
  have hg' : g ∈ genListZ ++ genListX := hg
  rcases List.mem_append.mp hg' with hz | hx
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact HomologicalCode.ZGenerators_subset_homologicalGenerators ⟨v, rfl⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact HomologicalCode.XGenerators_subset_homologicalGenerators ⟨f, rfl⟩

lemma gens_commute_packaged :
    ∀ g ∈ listToSet genListPackaged, ∀ h ∈ listToSet genListPackaged, g * h = h * g := by
  intro g hg h hh
  exact HomologicalCode.homologicalGenerators_commute g (listToSet_packaged_subset_homGens hg)
    h (listToSet_packaged_subset_homGens hh)

lemma gens_no_neg_packaged :
    negIdentity grossComplex.numQubits ∉ Subgroup.closure (listToSet genListPackaged) := by
  rw [closure_packaged_eq]
  exact grossComplex.homologicalStabilizerGroup.no_neg_identity

/-- The packaged stabilizer group. -/
noncomputable def packagedSG : StabilizerGroup grossComplex.numQubits :=
  mkStabilizerFromGenerators grossComplex.numQubits genListPackaged
    gens_commute_packaged gens_no_neg_packaged

lemma packagedSG_toSubgroup_eq :
    packagedSG.toSubgroup = grossComplex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- Indicator chain of the i-th X-logical support. -/
def logXchain (i : Fin 12) : GrossGroup × Fin 2 → ZMod 2 :=
  fun e => if e ∈ logX.getD i.val [] then 1 else 0

def logZchain (i : Fin 12) : GrossGroup × Fin 2 → ZMod 2 :=
  fun e => if e ∈ logZ.getD i.val [] then 1 else 0

/-- Computable form of `dualBoundary` on a 1-chain: the transpose of `∂₂`. -/
def dualBfn (c : GrossGroup × Fin 2 → ZMod 2) (f : GrossGroup) : ZMod 2 :=
  ∑ h : GrossGroup, (c (h, 0) * d2term f h 0 + c (h, 1) * d2term f h 1)

lemma dualBoundary_eq_dualBfn (c : GrossGroup × Fin 2 → ZMod 2) (f : GrossGroup) :
    grossComplex.dualBoundary c f = dualBfn c f := by
  rw [HomologicalCode.dualBoundary_apply]
  change (∑ e : GrossGroup × Fin 2,
    c e * grossComplex.boundary2 (grossComplex.singleFace f) e) = dualBfn c f
  unfold dualBfn
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fin.sum_univ_two, boundary2_singleFace_apply, boundary2_singleFace_apply]

/-- All 12 X-logicals are cycles. -/
lemma logXchain_cycle (i : Fin 12) : grossComplex.boundary1 (logXchain i) = 0 := by
  have h : ∀ k : Fin 12, bbBoundary1Fn grossA grossB (logXchain k) = 0 := by native_decide
  exact h i

/-- All 12 Z-logicals are dual cycles. -/
lemma logZchain_dualCycle (i : Fin 12) : grossComplex.dualBoundary (logZchain i) = 0 := by
  have h : ∀ k : Fin 12, ∀ f : GrossGroup, dualBfn (logZchain k) f = 0 := by native_decide
  funext f; rw [dualBoundary_eq_dualBfn]; exact h i f

/-- The 12×12 intersection matrix is the identity. -/
lemma logChain_inner (i j : Fin 12) :
    grossComplex.chainInnerProduct (logXchain i) (logZchain j) = (if i = j then 1 else 0) := by
  have h : ∀ a b : Fin 12,
      (∑ e : GrossGroup × Fin 2, logXchain a e * logZchain b e) = (if a = b then 1 else 0) := by
    native_decide
  exact h i j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The `i`-th logical qubit operator pair. -/
noncomputable def logicalQubit (i : Fin 12) :
    LogicalQubitOps grossComplex.numQubits packagedSG where
  xOp := grossComplex.chainXOperator (logXchain i)
  zOp := grossComplex.chainZOperator (logZchain i)
  x_mem_centralizer := by
    rw [centralizer_eq_of_toSubgroup_eq packagedSG grossComplex.homologicalStabilizerGroup
      packagedSG_toSubgroup_eq]
    exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles (logXchain i)).mpr
      ((grossComplex.mem_cycles_iff (logXchain i)).mpr (logXchain_cycle i))
  z_mem_centralizer := by
    rw [centralizer_eq_of_toSubgroup_eq packagedSG grossComplex.homologicalStabilizerGroup
      packagedSG_toSubgroup_eq]
    refine (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles (logZchain i)).mpr ?_
    show logZchain i ∈ LinearMap.ker grossComplex.dualBoundary
    rw [LinearMap.mem_ker]; exact logZchain_dualCycle i
  anticommute := by
    rcases NQubitPauliGroupElement.commute_or_anticommute
      (grossComplex.chainXOperator (logXchain i)) (grossComplex.chainZOperator (logZchain i))
      with hc | ha
    · exfalso
      have hip := (HomologicalCode.chainXOperator_commutes_chainZOperator_iff
        (logXchain i) (logZchain i)).mp hc
      rw [logChain_inner i i, if_pos rfl] at hip
      exact one_ne_zero hip
    · exact ha

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Logical operators for different logical qubits commute (the 12×12 matrix). -/
theorem logical_commute_cross : ∀ ℓ ℓ' : Fin 12, ℓ ≠ ℓ' →
    ((logicalQubit ℓ).xOp * (logicalQubit ℓ').xOp
        = (logicalQubit ℓ').xOp * (logicalQubit ℓ).xOp ∧
      (logicalQubit ℓ).xOp * (logicalQubit ℓ').zOp
        = (logicalQubit ℓ').zOp * (logicalQubit ℓ).xOp ∧
      (logicalQubit ℓ).zOp * (logicalQubit ℓ').xOp
        = (logicalQubit ℓ').xOp * (logicalQubit ℓ).zOp ∧
      (logicalQubit ℓ).zOp * (logicalQubit ℓ').zOp
        = (logicalQubit ℓ').zOp * (logicalQubit ℓ).zOp) := by
  intro ℓ ℓ' hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.XType_commutes
      (HomologicalCode.chainXOperator_isXType _) (HomologicalCode.chainXOperator_isXType _)
  · exact (HomologicalCode.chainXOperator_commutes_chainZOperator_iff
      (logXchain ℓ) (logZchain ℓ')).mpr (by rw [logChain_inner ℓ ℓ', if_neg hne])
  · exact ((HomologicalCode.chainXOperator_commutes_chainZOperator_iff
      (logXchain ℓ') (logZchain ℓ)).mpr
      (by rw [logChain_inner ℓ' ℓ, if_neg (Ne.symm hne)])).symm
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.ZType_commutes
      (HomologicalCode.chainZOperator_isZType _) (HomologicalCode.chainZOperator_isZType _)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The gross `[[144, 12, 12]]` bivariate-bicycle code as a `StabilizerCode`. -/
noncomputable def grossStabilizerCode : StabilizerCode grossComplex.numQubits 12 where
  hk := by rw [grossComplex_numQubits]; omega
  generatorsList := genListPackaged
  generators_length := by
    have h66 : keptCoords.length = 66 := by decide
    have hn := grossComplex_numQubits
    rw [genListPackaged_length]; omega
  generators_phaseZero := by
    intro g hg
    rcases List.mem_append.mp (show g ∈ genListZ ++ genListX from hg) with hz | hx
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact (HomologicalCode.vertexStabOf_isZType v).1
    · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact (HomologicalCode.faceStabOf_isXType f).1
  generators_independent := generators_independent_packaged
  generators_commute := gens_commute_packaged
  closure_no_neg_identity := gens_no_neg_packaged
  logicalOps := logicalQubit
  logical_commute_cross := logical_commute_cross

/-- The packaged code's stabilizer subgroup is the gross homological stabilizer
subgroup — the bridge that transports the chain-level distance theorems. -/
theorem grossStabilizerCode_toSubgroup_eq :
    grossStabilizerCode.toStabilizerGroup.toSubgroup
      = grossComplex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- **Unconditional lower bound**: every nontrivial logical operator of the
packaged gross code has weight ≥ 6 (triple the Lin–Pryadko floor). -/
theorem grossStabilizerCode_logical_weight_ge_6 (g : NQubitPauliGroupElement grossComplex.numQubits)
    (hg : IsNontrivialLogicalOperator g grossStabilizerCode.toStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  gross_logical_weight_ge_6 g
    ((IsNontrivialLogicalOperator_of_toSubgroup_eq g grossStabilizerCode_toSubgroup_eq).mp hg)

/-- **`HasCodeDistance grossStabilizerCode 12`**, conditional on the two CRT-engine
inputs (`LightStabilizerClassification`, `MImBound`). Everything else — the
packaging and the chain-level distance — is unconditional. -/
theorem grossStabilizerCode_hasCodeDistance_12
    (hC : LightStabilizerClassification) (hMim : MImBound) :
    HasCodeDistance grossStabilizerCode 12 := by
  have hleast := gross_pauli_distance_eq_12_of_engine hC hMim
  refine ⟨by norm_num, ?_, ?_⟩
  · intro g hg _
    exact hleast.2 ⟨g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g
      grossStabilizerCode_toSubgroup_eq).mp hg, rfl⟩
  · obtain ⟨g, hg, hw⟩ := hleast.1
    exact ⟨g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g
      grossStabilizerCode_toSubgroup_eq).mpr hg, hw⟩


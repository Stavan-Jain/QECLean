import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# The CSS distance bridge for homological codes

The distance of a homological CSS code is governed by the weights of its
homologically nontrivial chains. Every Pauli group element `g` has an
X-support chain `xChainOf g` and a Z-support chain `zChainOf g`, and:

* `weight_ge_chainWeight_xChainOf`, `weight_ge_chainWeight_zChainOf`: the Pauli
  weight of `g` bounds the `chainWeight` of both chains;
* `weight_chainXOperator`, `weight_chainZOperator`: a chain operator has the
  weight of its chain;
* `xChainOf_mem_cycles_of_centralizer`,
  `zChainOf_mem_dualCycles_of_centralizer`: if `g` commutes with the stabilizer
  group, `xChainOf g` is a cycle and `zChainOf g` a dual cycle;
* `not_both_boundary_of_nontrivial`: if `g` is a nontrivial logical operator,
  `xChainOf g` and `zChainOf g` are not both (dual) boundaries;
* `chainWeight_lower_bound_transfers`: a lower bound on the weight of the
  cycles that are not boundaries and of the dual cycles that are not dual
  boundaries is a lower bound on the weight of every nontrivial logical
  operator (`chainWeight_lower_bound_transfers_asymmetric` for two different
  bounds).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

/-- The support of a 1-chain: the edges where it is nonzero. -/
noncomputable def chainSupport (c : X.C1 → ZMod 2) : Finset X.C1 :=
  Finset.univ.filter (fun e => c e ≠ 0)

/-- The weight of a 1-chain: the size of its support. -/
noncomputable def chainWeight (c : X.C1 → ZMod 2) : ℕ := (X.chainSupport c).card

variable {X}

/-! ## Weights -/

/-- A chain whose support lies, edge by edge, in the support of a Pauli group
element has at most the weight of that element. -/
private lemma chainWeight_le_weight {c : X.C1 → ZMod 2}
    {g : NQubitPauliGroupElement X.numQubits}
    (h : ∀ e, c e ≠ 0 → g.operators (X.edgeEquiv e) ≠ PauliOperator.I) :
    X.chainWeight c ≤ NQubitPauliGroupElement.weight g :=
  Finset.card_le_card_of_injOn X.edgeEquiv
    (fun e he => Finset.mem_coe.2 <| (NQubitPauliOperator.mem_support _ _).2 <|
      h e (Finset.mem_filter.1 (Finset.mem_coe.1 he)).2)
    X.edgeEquiv.injective.injOn

/-- The weight of `g` is at least the weight of its X-support chain. -/
lemma weight_ge_chainWeight_xChainOf (g : NQubitPauliGroupElement X.numQubits) :
    NQubitPauliGroupElement.weight g ≥ X.chainWeight (X.xChainOf g) :=
  chainWeight_le_weight fun e he hI => he (by simp [xChainOf, hI])

/-- The weight of `g` is at least the weight of its Z-support chain. -/
lemma weight_ge_chainWeight_zChainOf (g : NQubitPauliGroupElement X.numQubits) :
    NQubitPauliGroupElement.weight g ≥ X.chainWeight (X.zChainOf g) :=
  chainWeight_le_weight fun e he hI => he (by simp [zChainOf, hI])

/-- `chainXOperator c` has the weight of `c`: `edgeEquiv` identifies the
support of the chain with the support of the operator. -/
lemma weight_chainXOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement.weight (X.chainXOperator c) = X.chainWeight c :=
  (Finset.card_equiv (s := X.chainSupport c)
    (t := (X.chainXOperator c).operators.support) X.edgeEquiv fun e => by
      rw [mem_support_chainXOperator_iff]
      simp [chainSupport, zmod2_ne_zero_iff]).symm

/-- `chainZOperator c` has the weight of `c`. -/
lemma weight_chainZOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement.weight (X.chainZOperator c) = X.chainWeight c :=
  (Finset.card_equiv (s := X.chainSupport c)
    (t := (X.chainZOperator c).operators.support) X.edgeEquiv fun e => by
      rw [mem_support_chainZOperator_iff]
      simp [chainSupport, zmod2_ne_zero_iff]).symm

/-! ## From the centralizer to cycles -/

/-- If `g` commutes with the stabilizer group, its X-support chain is a cycle:
commuting with the Z-check at `v` says `(∂₁ (xChainOf g)) v = 0`. -/
lemma xChainOf_mem_cycles_of_centralizer
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : g ∈ Quantum.StabilizerGroup.centralizer X.homologicalStabilizerGroup) :
    X.xChainOf g ∈ X.cycles := by
  refine (mem_cycles_iff _ _).2 (funext fun v => ?_)
  have h := (Quantum.StabilizerGroup.mem_centralizer_iff g _).1 hg _
    (X.closure_ZGenerators_le (Subgroup.subset_closure ⟨v, rfl⟩))
  rw [← chainInnerProduct_cutMap_singleVtx_eq_boundary1]
  exact (commutes_chainZOperator_iff g _).1 h.symm

/-- If `g` commutes with the stabilizer group, its Z-support chain is a dual
cycle: commuting with the X-check at `f` says
`(dualBoundary (zChainOf g)) f = 0`. -/
lemma zChainOf_mem_dualCycles_of_centralizer
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : g ∈ Quantum.StabilizerGroup.centralizer X.homologicalStabilizerGroup) :
    X.zChainOf g ∈ X.dualCycles := by
  refine LinearMap.mem_ker.2 (funext fun f => ?_)
  have h := (Quantum.StabilizerGroup.mem_centralizer_iff g _).1 hg _
    (X.closure_XGenerators_le (Subgroup.subset_closure ⟨f, rfl⟩))
  rw [← chainInnerProduct_boundary2_singleFace_eq_dualBoundary]
  exact (chainXOperator_commutes_iff _ g).1 h

/-! ## Nontrivial logical operators -/

/-- For a nontrivial logical operator `g`, the X-support chain and the
Z-support chain are not both (dual) boundaries: otherwise the product of the
X-only and Z-only parts of `g` would be a stabilizer element with the operator
part of `g`. -/
theorem not_both_boundary_of_nontrivial
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    ¬ (X.xChainOf g ∈ X.boundaries ∧ X.zChainOf g ∈ X.dualBoundaries) := by
  rintro ⟨hx, hz⟩
  refine hg.2 (X.chainXOperator (X.xChainOf g) * X.chainZOperator (X.zChainOf g))
    (mul_mem
      (X.closure_XGenerators_le ((chainXOperator_mem_XClosure_iff_mem_boundaries _).2 hx))
      (X.closure_ZGenerators_le ((chainZOperator_mem_ZClosure_iff_mem_dualBoundaries _).2 hz)))
    (funext fun i => ?_)
  change (((X.chainXOperator (X.xChainOf g)).operators i).mulOp
    ((X.chainZOperator (X.zChainOf g)).operators i)).operator = g.operators i
  rw [chainXOperator_xChainOf_op_at, chainZOperator_zChainOf_op_at]
  generalize g.operators i = P
  cases P <;> decide

/-- If every cycle that is not a boundary and every dual cycle that is not a
dual boundary has chain weight at least `K`, then every nontrivial logical
operator has weight at least `K`. -/
theorem chainWeight_lower_bound_transfers
    (X : HomologicalCode) (K : ℕ)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → K ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → K ≤ X.chainWeight c)
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    K ≤ NQubitPauliGroupElement.weight g := by
  by_cases hx : X.xChainOf g ∈ X.boundaries
  · exact (hZ _ (zChainOf_mem_dualCycles_of_centralizer g hg.1) fun hz =>
      not_both_boundary_of_nontrivial g hg ⟨hx, hz⟩).trans (weight_ge_chainWeight_zChainOf g)
  · exact (hX _ (xChainOf_mem_cycles_of_centralizer g hg.1) hx).trans
      (weight_ge_chainWeight_xChainOf g)

/-- The form of `chainWeight_lower_bound_transfers` with separate bounds `K_X`
on the cycles and `K_Z` on the dual cycles: every nontrivial logical operator
has weight at least `min K_X K_Z`. -/
theorem chainWeight_lower_bound_transfers_asymmetric
    (X : HomologicalCode) (K_X K_Z : ℕ)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → K_X ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → K_Z ≤ X.chainWeight c)
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    min K_X K_Z ≤ NQubitPauliGroupElement.weight g :=
  chainWeight_lower_bound_transfers X _
    (fun c hc hnb => (min_le_left _ _).trans (hX c hc hnb))
    (fun c hc hnb => (min_le_right _ _).trans (hZ c hc hnb)) g hg

end HomologicalCode

end Homological
end Stabilizer
end Quantum

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

The file opens with a way to produce such lower bounds,
`card_le_card_support_of_fiber_parity`. Let `B ≤ Z` be spaces of
`ZMod 2`-valued chains with `dim Z ≤ dim B + 1`, and let the cells be
partitioned into lines, the fibers of a map `π`. If every element of `B` has
an even number of cells on every line, and some element of `Z` has an odd
number of cells on every line, then so has every element of `Z` outside `B`
(`apply_ne_zero_of_finrank_le_succ`), which therefore has at least as many
cells as there are lines (`card_le_card_support_of_fiber_sum_ne_zero`).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators
open scoped Homology

/-! ## A weight bound from line parities -/

/-- A linear functional that vanishes on a subspace `B` of codimension at most
one in `Z`, but not on all of `Z`, is nonzero at every element of `Z` outside
`B`: its kernel in `Z` is a proper subspace containing `B`, hence equal to
`B`. -/
lemma apply_ne_zero_of_finrank_le_succ {K M : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] {Z B : Submodule K M} (hBZ : B ≤ Z)
    (hdim : Module.finrank K Z ≤ Module.finrank K B + 1) (ψ : M →ₗ[K] K)
    (hB : ∀ b ∈ B, ψ b = 0) {m : M} (hm : m ∈ Z) (hψm : ψ m ≠ 0)
    {c : M} (hc : c ∈ Z) (hcB : c ∉ B) : ψ c ≠ 0 := by
  have hlt : Z ⊓ LinearMap.ker ψ < Z :=
    lt_of_le_of_ne inf_le_left fun h => hψm (LinearMap.mem_ker.1 (h.ge hm).2)
  have hBK : B = Z ⊓ LinearMap.ker ψ :=
    Submodule.eq_of_le_of_finrank_le (le_inf hBZ fun b hb => LinearMap.mem_ker.2 (hB b hb))
      (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega)
  exact fun h => hcB (hBK.ge ⟨hc, LinearMap.mem_ker.2 h⟩)

/-- A `ZMod 2`-valued chain with an odd number of cells on every fiber of `π`
has at least as many cells as `π` has fibers. -/
lemma card_le_card_support_of_fiber_sum_ne_zero {V κ : Type*} [Fintype V] [Fintype κ]
    [DecidableEq κ] (π : V → κ) {c : V → ZMod 2} (h : ∀ y, ∑ v with π v = y, c v ≠ 0) :
    Fintype.card κ ≤ (Finset.univ.filter fun v => c v ≠ 0).card := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_surjOn π fun y _ => ?_
  obtain ⟨v, hv, hcv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h y)
  exact ⟨v, by simpa using hcv, (Finset.mem_filter.1 hv).2⟩

/-- **Line-parity bound.** Let `B ≤ Z` be spaces of `ZMod 2`-valued chains
with `dim Z ≤ dim B + 1`, and call the fibers of `π` lines. If every chain in
`B` has an even number of cells on every line and some chain `m` in `Z` has an
odd number of cells on every line, then so has every chain in `Z` outside `B`,
whose support therefore has at least as many cells as there are lines. -/
theorem card_le_card_support_of_fiber_parity {V κ : Type*} [Fintype V] [Fintype κ]
    [DecidableEq κ] (π : V → κ) {Z B : Submodule (ZMod 2) (V → ZMod 2)} (hBZ : B ≤ Z)
    (hdim : dim₂ Z ≤ dim₂ B + 1) (hB : ∀ b ∈ B, ∀ y, ∑ v with π v = y, b v = 0)
    {m : V → ZMod 2} (hm : m ∈ Z) (hm1 : ∀ y, ∑ v with π v = y, m v = 1)
    {c : V → ZMod 2} (hc : c ∈ Z) (hcB : c ∉ B) :
    Fintype.card κ ≤ (Finset.univ.filter fun v => c v ≠ 0).card := by
  refine card_le_card_support_of_fiber_sum_ne_zero π fun y => ?_
  let ψ : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ v with π v = y, LinearMap.proj v
  have hψ : ∀ a, ψ a = ∑ v with π v = y, a v := fun a => by simp [ψ]
  have h := apply_ne_zero_of_finrank_le_succ hBZ hdim ψ (fun b hb => (hψ b).trans (hB b hb y))
    hm (by rw [hψ, hm1]; exact one_ne_zero) hc hcB
  rwa [hψ] at h

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

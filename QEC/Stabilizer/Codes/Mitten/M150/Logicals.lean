import QEC.Stabilizer.Codes.Mitten.M150.StabilizerCode
import QEC.Stabilizer.Codes.Mitten.M150.SparseSupport

/-!
# Thirty logical pairs for the mitten code

The generated support tables give cycles and dual cycles with identity
pairing matrix. Sparse support checks certify their syndromes and pairings,
which produce logical operators for the canonical stabilizer group.
-/

namespace Quantum.Stabilizer.Homological.LP.M150
open Quantum.StabilizerGroup
open scoped BigOperators
local notation "packagedSG" => m150StabilizerCode.toStabilizerGroup

/-- Centralizer membership for an X-chain operator, **chain abstract**: the
stuck `c` blocks `m150Complex.chainXOperator` from reducing and `packagedSG`
stays behind `m150StabilizerCode_toSubgroup_eq`, so the `centralizer`-transport defeq
is paid once here. -/
lemma chainXOperator_mem_centralizer_packagedSG (c : m150Complex.C1 → ZMod 2)
    (hc : m150Complex.boundary1 c = 0) :
    m150Complex.chainXOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG m150Complex.homologicalStabilizerGroup
    m150StabilizerCode_toSubgroup_eq]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles c).mpr
    ((m150Complex.mem_cycles_iff c).mpr hc)

/-- Centralizer membership for a Z-chain operator (chain abstract; mirror of
the X case). -/
lemma chainZOperator_mem_centralizer_packagedSG (c : m150Complex.C1 → ZMod 2)
    (hc : m150Complex.dualBoundary c = 0) :
    m150Complex.chainZOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG m150Complex.homologicalStabilizerGroup
    m150StabilizerCode_toSubgroup_eq]
  refine (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles c).mpr ?_
  change c ∈ LinearMap.ker m150Complex.dualBoundary
  rw [LinearMap.mem_ker]
  exact hc

/-- An X-chain and a Z-chain operator anticommute when their inner product is
`1` (chains abstract). -/
lemma chainXOperator_anticommute_chainZOperator (c c' : m150Complex.C1 → ZMod 2)
    (h : m150Complex.chainInnerProduct c c' = 1) :
    NQubitPauliGroupElement.Anticommute
      (m150Complex.chainXOperator c) (m150Complex.chainZOperator c') := by
  rcases NQubitPauliGroupElement.commute_or_anticommute
    (m150Complex.chainXOperator c) (m150Complex.chainZOperator c') with hcomm | ha
  · exfalso
    have hzero := (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mp hcomm
    rw [h] at hzero
    exact one_ne_zero hzero
  · exact ha

/-- An X-chain and a Z-chain operator commute when their inner product is `0`
(chains abstract). -/
lemma chainXOperator_commute_chainZOperator (c c' : m150Complex.C1 → ZMod 2)
    (h : m150Complex.chainInnerProduct c c' = 0) :
    m150Complex.chainXOperator c * m150Complex.chainZOperator c'
      = m150Complex.chainZOperator c' * m150Complex.chainXOperator c :=
  (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mpr h

/-- Indicator chain of the `i`-th X-logical support (row `i` of `Lx`). -/
def logXchain (i : Fin 30) : Fin 5 × M150G → ZMod 2 :=
  supportChain (logXsup.getD i.val [])

/-- Indicator chain of the `i`-th Z-logical support (row `i` of `Lz`). -/
def logZchain (i : Fin 30) : Fin 5 × M150G → ZMod 2 :=
  supportChain (logZsup.getD i.val [])

/-- Every listed X-logical support has zero sparse syndrome. -/
private lemma logX_checks : ∀ k : Fin 30, ∀ p : Fin 2 × M150G,
    (∑ q ∈ ((logXsup.getD k.val []).map qubitOf).toFinset, cmTerm p q) = 0 := by
  decide +kernel

/-- Every listed Z-logical support has zero sparse dual syndrome. -/
private lemma logZ_checks : ∀ k : Fin 30, ∀ p : Fin 2 × M150G,
    (∑ q ∈ ((logZsup.getD k.val []).map qubitOf).toFinset, d2term p q) = 0 := by
  decide +kernel

/-- All thirty X-logical chains are cycles. -/
lemma logXchain_cycle (i : Fin 30) : m150Complex.boundary1 (logXchain i) = 0 := by
  funext p
  exact (boundary1_supportChain (logXsup.getD i.val []) p).trans (logX_checks i p)

/-- All thirty Z-logical chains are dual cycles. -/
lemma logZchain_dualCycle (i : Fin 30) : m150Complex.dualBoundary (logZchain i) = 0 := by
  funext p
  exact (dualBoundary_supportChain (logZsup.getD i.val []) p).trans (logZ_checks i p)

/-- The thirty logical support pairs have the identity intersection matrix. -/
private lemma log_pairings : ∀ a b : Fin 30,
    (∑ q ∈ ((logXsup.getD a.val []).map qubitOf).toFinset, logZchain b q) =
      (if a = b then 1 else 0) := by
  decide +kernel

/-- The logical intersection matrix is the identity. -/
lemma logChain_inner (i j : Fin 30) :
    m150Complex.chainInnerProduct (logXchain i) (logZchain j) =
      (if i = j then 1 else 0) := by
  change (∑ q, supportChain (logXsup.getD i.val []) q * logZchain j q) = _
  rw [supportChain_pairing]
  exact log_pairings i j

set_option maxRecDepth 4096 in
/-- The `i`-th logical qubit operator pair: the abstract helpers above are
simply *applied* to the concrete chains, so no heavy defeq is re-run here. -/
noncomputable def logicalQubit (i : Fin 30) :
    LogicalQubitOps m150Complex.numQubits packagedSG where
  xOp := m150Complex.chainXOperator (logXchain i)
  zOp := m150Complex.chainZOperator (logZchain i)
  x_mem_centralizer := chainXOperator_mem_centralizer_packagedSG (logXchain i) (logXchain_cycle i)
  z_mem_centralizer :=
    chainZOperator_mem_centralizer_packagedSG (logZchain i) (logZchain_dualCycle i)
  anticommute := chainXOperator_anticommute_chainZOperator (logXchain i) (logZchain i)
    (by rw [logChain_inner i i, if_pos rfl])

set_option maxRecDepth 4096 in
/-- Logical operators for different logical qubits commute (the `30×30`
matrix is diagonal off the diagonal). -/
theorem logical_commute_cross : ∀ ℓ ℓ' : Fin 30, ℓ ≠ ℓ' →
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
  · exact chainXOperator_commute_chainZOperator (logXchain ℓ) (logZchain ℓ')
      (by rw [logChain_inner ℓ ℓ', if_neg hne])
  · exact (chainXOperator_commute_chainZOperator (logXchain ℓ') (logZchain ℓ)
      (by rw [logChain_inner ℓ' ℓ, if_neg (Ne.symm hne)])).symm
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.ZType_commutes
      (HomologicalCode.chainZOperator_isZType _) (HomologicalCode.chainZOperator_isZType _)

/-- The canonical mitten code equipped with its thirty certified logical pairs. -/
noncomputable def m150StabilizerCodeWithLogicals : StabilizerCodeWithLogicals 150 30 where
  toStabilizerCode := m150StabilizerCode
  logicalOps := logicalQubit
  logical_commute_cross := logical_commute_cross

end Quantum.Stabilizer.Homological.LP.M150

#print axioms Quantum.Stabilizer.Homological.LP.M150.m150StabilizerCodeWithLogicals

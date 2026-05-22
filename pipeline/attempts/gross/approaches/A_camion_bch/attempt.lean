/-
# Approach A — Camion BCH multivariate apparent-distance bound

This file is the **exploration entry point** for Approach A.  The
core abstractions live in `QEC/Stabilizer/Homological/BBChainComplex.lean`
(promoted there because they are durable repo infrastructure rather
than throwaway scratch).

## What this file contains

1. **Abstract distance bridge**
   `chainWeight_lower_bound_transfers` — a purely homological lemma:
   if every non-boundary X-cycle has chain weight ≥ K and every
   non-dual-boundary Z-cycle has chain weight ≥ K, then every
   nontrivial logical operator has Pauli weight ≥ K.

2. **Gross code instantiation**
   `grossHomologicalCode : HomologicalCode` built from the BB chain
   complex with polynomials `A = x^3 + y + y^2`, `B = y^3 + x + x^2`
   over `Z_12 × Z_6`.  Number of qubits = 144.

## What this file does NOT yet contain

* The Camion apparent-distance bound itself (`K_X`, `K_Z`).  That is
  Step 3 of the plan, blocked by significant group-algebra
  infrastructure (Fourier analysis on `F_2[Z_ℓ × Z_m]`, CRT
  decomposition in the modular setting).
* A specific numerical lower bound on `grossHomologicalCode.distance`.
  Without Camion, we have only the trivial `d ≥ 1`.

The `final_writeup.md` for this approach calibrates honestly: this is
a Partial-C outcome (BB chain-complex scaffolding + abstract distance
bridge in Lean), not Partial-A.
-/

import QEC.Stabilizer.Homological

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

/-! ## Abstract chain-weight → Pauli-weight bridge

The key fact: for any non-trivial logical `g`, at least one of
`xChainOf g` or `zChainOf g` is *not* a boundary
(`not_both_boundary_of_nontrivial`).

Moreover, `g ∈ centralizer` forces `xChainOf g ∈ cycles` and
`zChainOf g ∈ dualCycles` (the centralizer→cycle bridges).

Therefore, if every non-boundary cycle has weight `≥ K`, then
`weight g ≥ K`. -/

/-- A lower bound on chain weight transfers to a lower bound on
Pauli weight, for any non-trivial logical operator on a homological CSS
code. -/
theorem chainWeight_lower_bound_transfers
    (K : ℕ)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → K ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → K ≤ X.chainWeight c)
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    K ≤ NQubitPauliGroupElement.weight g := by
  have hg_centralizer : g ∈ Quantum.StabilizerGroup.centralizer
      X.homologicalStabilizerGroup := by
    rw [Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff] at hg
    exact hg.1
  have hxCyc : X.xChainOf g ∈ X.cycles :=
    xChainOf_mem_cycles_of_centralizer g hg_centralizer
  have hzCyc : X.zChainOf g ∈ X.dualCycles :=
    zChainOf_mem_dualCycles_of_centralizer g hg_centralizer
  have hnot_both := not_both_boundary_of_nontrivial g hg
  rcases Classical.em (X.xChainOf g ∈ X.boundaries) with hxBnd | hxNotBnd
  · have hzNotBnd : X.zChainOf g ∉ X.dualBoundaries := by
      intro hzBnd
      exact hnot_both ⟨hxBnd, hzBnd⟩
    exact (hZ _ hzCyc hzNotBnd).trans (weight_ge_chainWeight_zChainOf g)
  · exact (hX _ hxCyc hxNotBnd).trans (weight_ge_chainWeight_xChainOf g)

/-- Asymmetric variant: separate `K_X` and `K_Z` bounds, conclusion uses
`min K_X K_Z`. Useful when the two sides of the CSS code have genuinely
different distance bounds. -/
theorem chainWeight_lower_bound_transfers_asymmetric
    (K_X K_Z : ℕ)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → K_X ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → K_Z ≤ X.chainWeight c)
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    min K_X K_Z ≤ NQubitPauliGroupElement.weight g := by
  have hX' : ∀ c ∈ X.cycles, c ∉ X.boundaries →
      min K_X K_Z ≤ X.chainWeight c := fun c hc hnb =>
    (min_le_left _ _).trans (hX c hc hnb)
  have hZ' : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries →
      min K_X K_Z ≤ X.chainWeight c := fun c hc hnb =>
    (min_le_right _ _).trans (hZ c hc hnb)
  exact chainWeight_lower_bound_transfers X _ hX' hZ' g hg

end HomologicalCode

/-! ## The IBM Gross code

`grossHomologicalCode` is built from the BB chain complex with the
polynomial pair `A = x^3 + y + y^2`, `B = y^3 + x + x^2` over
`F_2[Z_12 × Z_6]`.  The chain complex law `∂₁ ∘ ∂₂ = 0` is automatic
from `BB.bbBoundary_comp`. -/

namespace BB
namespace Gross

/-- The group `G = Z_12 × Z_6` for the gross code. -/
abbrev GrossGroup : Type := ZMod 12 × ZMod 6

/-- Polynomial `A(x, y) = x^3 + y + y^2`, as an indicator function. -/
def grossA : GrossGroup → ZMod 2
  | (3, 0) => 1
  | (0, 1) => 1
  | (0, 2) => 1
  | _      => 0

/-- Polynomial `B(x, y) = y^3 + x + x^2`, as an indicator function. -/
def grossB : GrossGroup → ZMod 2
  | (0, 3) => 1
  | (1, 0) => 1
  | (2, 0) => 1
  | _      => 0

/-- The gross code as a `HomologicalCode`. Has 144 qubits via the
`bbChainComplex` construction over `G = Z_12 × Z_6`. -/
noncomputable def grossHomologicalCode : HomologicalCode :=
  bbChainComplex (G := GrossGroup) grossA grossB

/-- The gross code has 144 physical qubits. -/
@[simp] lemma grossHomologicalCode_numQubits :
    grossHomologicalCode.numQubits = 144 := by
  change bbNumQubits GrossGroup = 144
  unfold bbNumQubits
  decide

end Gross
end BB

end Homological
end Stabilizer
end Quantum

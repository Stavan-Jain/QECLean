/-
# Approach A — Camion BCH multivariate apparent-distance bound

This file is the **exploration entry point** for Approach A.  The
core abstractions live in `QEC/Stabilizer/Framework/Homological/BBChainComplex.lean`
(promoted there because they are durable repo infrastructure rather
than throwaway scratch). The abstract chain-weight → Pauli-weight
distance bridge `chainWeight_lower_bound_transfers` was also promoted
into `QEC/Stabilizer/Framework/Homological/Distance.lean` (where its building
blocks already lived) — see the symmetric and asymmetric variants there.

## What this file contains

1. **Gross code instantiation**
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

import QEC.Stabilizer.Framework.Homological

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

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

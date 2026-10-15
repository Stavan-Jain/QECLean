/-
# The gross code's distance capstones

The human-facing results of the gross `[[144,12,12]]` formalization, in one
hand-written file (every instance keeps its
results in `Distance.lean` / `StabilizerCode.lean`). Both certificate inputs —
`MImBound` and `LightStabilizerClassification` — are discharged by one
Brouwer–Zimmermann certificate (`SeamBZ.lean`). `LayerInstance.lean` derives the
distance through the packaged Doubling theorem of the parametric layer; the
results here transport that proof to the packaged stabilizer code.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LayerInstance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCode

namespace Quantum.Stabilizer.Homological.BB

/-- **`HasCodeDistance grossStabilizerCode 12`**, conditional only on
`MImBound` (the light-stabilizer classification is discharged by
`GrossBZ.lightStabilizerClassification_bz`). Kept as the engine-route statement;
`grossStabilizerCode_hasCodeDistance_12_uncond` below is unconditional. -/
theorem grossStabilizerCode_hasCodeDistance_12 (hMim : MImBound) :
    Quantum.StabilizerGroup.HasCodeDistance grossStabilizerCode 12 :=
  Quantum.StabilizerGroup.has_code_distance_of_isLeast grossStabilizerCode
    grossStabilizerCode_toSubgroup_eq (by decide)
    (gross_pauli_distance_eq_12_of_engine GrossBZ.lightStabilizerClassification_bz hMim)

/-- **Unconditional `HasCodeDistance grossStabilizerCode 12`** — the Gross
`[[144,12,12]]` bivariate-bicycle code has distance exactly 12, with NO
remaining assumed hypotheses: both certificate inputs come from the
Brouwer–Zimmermann certificate `GrossBZ.grossSeamBZ`.
The distance proof is `gross_pauli_distance_eq_12`, one application of the
generic Doubling theorem `pauli_distance_eq_double_of_admissible`.
**Kernel-only**: the axioms are exactly `propext`, `Classical.choice` and
`Quot.sound` — no `native_decide`, no `sorry`. -/
theorem grossStabilizerCode_hasCodeDistance_12_uncond :
    Quantum.StabilizerGroup.HasCodeDistance grossStabilizerCode 12 :=
  Quantum.StabilizerGroup.has_code_distance_of_isLeast grossStabilizerCode
    grossStabilizerCode_toSubgroup_eq (by decide) gross_pauli_distance_eq_12

/-- **The Gross `[[144, 12, 12]]` code as a fully-parametrized object.** Bundles
the stabilizer code (`StabilizerCode 144 12`) with its now-unconditional
distance proof into a single `StabilizerCodeWithDistance` carrying all three
`[[n, k, d]]` parameters in its type. -/
noncomputable def grossStabilizerCodeWithDistance :
    Quantum.StabilizerGroup.StabilizerCodeWithDistance 144 12 12 where
  toStabilizerCode := grossStabilizerCode
  hasDistance := grossStabilizerCode_hasCodeDistance_12_uncond

end Quantum.Stabilizer.Homological.BB

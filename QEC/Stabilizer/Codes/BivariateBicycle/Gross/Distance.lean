/-
# The gross code's distance capstones

The human-facing results of the gross `[[144,12,12]]` formalization, in one
hand-written file (every instance keeps its
results in `Distance.lean` / `StabilizerCode.lean`). The inputs are
discharged upstream: `MImBound` by `SafeFloor/MImAssembly.lean`
(`LightStab.mimBound_holds`), `LightStabilizerClassification` by
`LightStabClassify.lean`. `LayerInstance.lean` derives the distance through
the parametric doubling layer; the results here transport that proof to the
packaged stabilizer code.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LayerInstance

namespace Quantum.Stabilizer.Homological.BB

/-- **Unconditional `HasCodeDistance grossStabilizerCode 12`** — the Gross
`[[144,12,12]]` bivariate-bicycle code has distance exactly 12, with NO
remaining assumed hypotheses. The last analytic input `MImBound` is discharged
by `LightStab.mimBound_holds`; the `LightStabilizerClassification` input was
discharged earlier by `LightStab.lightStabilizerClassification_holds`.
The distance proof is `gross_pauli_distance_eq_12` from the generic layer.
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

import QEC.Stabilizer.Framework.Concatenation
import QEC.Stabilizer.Codes.Small.Steane7

/-!
# Steane ⊗ Steane: the concatenated `[[49, 1, ≥ 9]]` instance (Milestone M7)

The validating concrete instance of the CSS concatenation framework
(`pipeline/attempts/concat_css_general/plan.md`): concatenate the Steane `[[7,1,3]]` code with
itself. `steaneConcatData` bundles `Steane7.stabilizerCode` as both inner and outer code into a
`ConcatCSSData 7 7 1` — the data the whole framework consumes.

## Status and the two instantiation blockers

`steaneConcatData` typechecks (below), so the framework's input bundle instantiates on a real
code. Producing the full `StabilizerCode 49 1` via `concatenate` and its distance, however, runs
into two obstacles that are **framework gaps, not flaws in M1–M6**:

1. **Generator independence is not `native_decide`-able.** `concatenate` requires
   `GeneratorsIndependent 49 concatGeneratorsList`. The only available decision procedure,
   `Decidable (rowsLinearIndependent L)` (`CheckMatrixDecidable.lean`), enumerates *all*
   `2 ^ L.length` coefficient vectors. The concatenated list has `49 − 1 = 48` generators, so
   that is `2⁴⁸` — infeasible (OOM). The plan's "`native_decide` per instance" fallback (risk
   R5) works only for small single codes (Steane itself: `2⁶`); it does **not** scale to the
   concatenated code. The real fix is a *structural* `rowsLinearIndependent_concat` lemma
   deriving concat-independence from the inner/outer independence and the disjoint block-support
   of the embedded inner generators — a new framework lemma (≈ M4-scale), not a decision.

2. **The inner/outer distance `HasCodeDistance Steane7.stabilizerCode 3` is not yet formalized.**
   `concat_hasCodeDistance` (M6) consumes it (as `h1`, `h2`) plus a weight-9 witness. Steane's
   own distance-3 proof (a min-weight argument over weight-1 and weight-2 Paulis) is a separate
   task; it `native_decide`s comfortably at `n = 7` but is not present in the repo.

Both are recorded in `pipeline/attempts/concat_css_general/state.yaml`. The abstract framework
(M1–M6) is complete and sorry-free; these blockers concern only the *concrete discharge* of its
hypotheses.
-/

namespace Quantum.StabilizerGroup.Steane7

open Quantum.Concatenation NQubitPauliGroupElement

/-- The Steane ⊗ Steane concatenation data: `Steane7.stabilizerCode` as both inner and outer
code, with the CSS `Z`/`X` generator split `[Z1,Z2,Z3] ++ [X1,X2,X3]` and the all-`X` / all-`Z`
phase-0 logicals. This is the `ConcatCSSData` bundle the whole framework consumes; it typechecks,
validating that the framework's input shape instantiates on the Steane code. -/
noncomputable def steaneConcatData : ConcatCSSData 7 7 1 where
  Cin := stabilizerCode
  Cout := stabilizerCode
  innerZ := [Z1, Z2, Z3]
  innerX := [X1, X2, X3]
  inner_split := List.Perm.refl _
  innerZ_isZ := fun g hg => ZGenerators_are_ZType g (by simpa [ZGenerators] using hg)
  innerX_isX := fun g hg => XGenerators_are_XType g (by simpa [XGenerators] using hg)
  outerZ := [Z1, Z2, Z3]
  outerX := [X1, X2, X3]
  outer_split := List.Perm.refl _
  outerZ_isZ := fun g hg => ZGenerators_are_ZType g (by simpa [ZGenerators] using hg)
  outerX_isX := fun g hg => XGenerators_are_XType g (by simpa [XGenerators] using hg)
  innerLogX_isX := fun _ => Or.inr rfl
  innerLogX_phaseZero := rfl
  innerLogZ_isZ := fun _ => Or.inr rfl
  innerLogZ_phaseZero := rfl
  outerLogX_isX := fun _ _ => Or.inr rfl
  outerLogZ_isZ := fun _ _ => Or.inr rfl

end Quantum.StabilizerGroup.Steane7

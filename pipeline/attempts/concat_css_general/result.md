# concat_css_general — result

**Status: complete (pr-ready), sorry-free.** Parametric CSS concatenation
`[[n₁n₂, k₂, ≥ d₁d₂]]` for inner `[[n₁,1,d₁]]` × outer `[[n₂,k₂,d₂]]` CSS
codes, with two unconditional validating instances. (This file was
back-filled 2026-07-18 during repo cleanup from `state.yaml` — the program
had completed with every milestone recorded there but no result.md.)

## What landed

- **Abstract framework (M1–M6)** — `QEC/Stabilizer/Framework/Concatenation/`
  (umbrella `Framework/Concatenation.lean`): the concatenation constructor,
  structural independence (`rowsLinearIndependent_concat` /
  `generatorsIndependent_concat`, axiom-clean), and the headline
  `concat_hasCodeDistance : HasCodeDistance (concatenate D) (d1 * d2)`
  (`Concatenation/Distance.lean`).
- **Packaging** — `ConcatCSSData.concatenateWithDistance` bundles any
  discharged instance as `StabilizerCodeWithDistance (n1*n2) k2 (d1*d2)`.
- **Instances** (`QEC/Stabilizer/Codes/Concat/`), both unconditional, no
  `sorryAx` (standard three axioms + `native_decide`):
  - `steaneConcatCodeWithDistance : StabilizerCodeWithDistance 49 1 9`
    (Steane ⊗ Steane; witness = X on inner {3,5,6} of outer blocks {3,5,6}).
  - `steane422CodeWithDistance : StabilizerCodeWithDistance 28 2 6`
    (Steane ⊗ [[4,2,2]]; exercises the k₂ > 1 path end-to-end).

## Milestones

M1–M7 all complete; 73 sorries closed over the program, 0 open. See
`state.yaml` (`long_pole`) for the full discharge record of the three
`concat_hasCodeDistance` inputs per instance.

## Patterns discovered

Promotion candidates recorded in `state.yaml → next_step`:
`blockRestrictSymp`, append-independence, the
noncomputable→concrete+`rfl`+`native_decide` bridge, and the k₂>1 witness
recipe (inner support on the blocks of an outer logical representative).

## Remaining generalization opportunities (not started)

- Drop k₁ = 1 to general inner `[[n₁,k₁,d₁]]` (major: the M4 centralizer
  classification is k₁ = 1-specific).
- Further instances (e.g. Shor ⊗ Steane `[[63,1,9]]`).

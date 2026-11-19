# Changelog

QECLean follows [semantic versioning](https://semver.org/) with `v0.MINOR.PATCH`
tags. Below 1.0, a **MINOR** bump means a breaking change to the public API (a
declaration renamed, removed, or restated), and a **PATCH** bump means
proof-only, documentation, or performance changes. Every breaking change is
listed under *Breaking*, old name → new name where there is one.

The `v4.x` tags (`v4.30.0-rc2`, `v4.36.0-rc2`) are a separate scheme: Lean
toolchain tags, set automatically when `lean-toolchain` changes. Each release
below records the toolchain and mathlib revision it was built against.

See [RELEASING.md](RELEASING.md) for how to cut a release.

## [Unreleased]

## [0.2.0] — 2026-11-19

The first versioned release. Changes are relative to the toolchain tag
`v4.36.0-rc2` (`ba47965`), the last tagged state of the library.

Built with Lean `v4.36.0-rc2` and mathlib `527b85a` (pinned in
`lake-manifest.json`).

### Added

- `Framework/Symplectic/DistanceDecide.lean`: the distance of a code given by a
  literal presentation, by `decide`. `presentation.hasCodeDistance_of_decide g
  (by decide +kernel) (by decide +kernel)` is the whole proof, for any `d`, CSS
  or not, degenerate or not. Supporting API: `NQubitPauliOperator.ofWeight`
  (all operators of a given weight, `mem_ofWeight`), `NQubitPauliOperator.cons`,
  `InSpan` / `inSpan_iff`, `Harmless`, `NoLogicalBelow`, `IsLogicalWitness`,
  `isNontrivialLogicalOperator_of_isLogicalWitness` (no anticommuting partner
  needed), `not_isNontrivialLogicalOperator_of_harmless`.
- `StabilizerCode.Presentation.mem_centralizer_iff`: centralizer membership as
  commuting with each generator, so `presentation.mem_centralizer_iff.2
  (by decide)` for a literal code.
- `commute_list_of_listToSet_eq`: pairwise commutation over a list from the
  same statement over a set with the same elements.
- `CHANGELOG.md`, `CITATION.cff`, `RELEASING.md`, and a release workflow that
  checks the tag against `lakefile.toml` and `CITATION.cff`.

### Changed

- Every file is a Lean module (`module`, `public import`, `@[expose] public
  section`). A downstream *module* must `public import` QECLean modules; a
  plain (non-module) file can still `import` them.
- Pairwise commutation is stated over list membership (`∀ g ∈ L, ∀ h ∈ L, …`)
  everywhere: `StabilizerCode.Presentation.generators_commute`,
  `mkStabilizerFromGenerators`, and the `−I` lemmas. `listToSet` appears only
  under `Subgroup.closure`.
- The small literal codes (`Small/FiveQubit_5_1_3`, `Small/Shor9`,
  `Small/FourQubit_4_2_2`, `Small/SixQubit_6_2_2`, `Small/CSS_4_1_2`) prove
  their distance with `hasCodeDistance_of_decide`; `Small/Steane7` keeps the
  column condition. All seven literal codes (with `Repetition/Three`) decide
  their presentation fields inline.

### Breaking

Framework:

- Removed `instDecidablePairwiseCommuteListToSet` (commutation is stated over
  the list; `instDecidablePairwiseCommute` decides it).
- `mkStabilizerFromGenerators` and the `−I` lemmas take
  `h_comm : ∀ g ∈ L, ∀ h ∈ L, g * h = h * g` instead of the `listToSet` form.
  Bridge an old-form proof with `commute_list_of_listToSet_eq`.

Per code (in the code's namespace):

- `stabilizerGroup`, `stabilizerGroup_toSubgroup_eq`, `negIdentity_not_mem` in
  `Codes/Small/`, `Repetition/`, `Iceberg/N` and `QuantumHamming` → removed. Use
  `stabilizerCode.toStabilizerGroup`; `−I` is the presentation's default field.
  `Toric` and `RotatedSurface` keep their `stabilizerGroup`;
  `Toric.negIdentity_not_mem_packaged` → removed.
- `mem_centralizer_of_commute_list stabilizerGroup_toSubgroup_eq h` →
  `presentation.mem_centralizer_iff.2 h`.
- `stabilizerCode_toSubgroup_eq` (literal codes) → `presentation.toCode_toSubgroup`.
  The parametric families keep theirs.
- `generators_commute`, `AllPhaseZero_generatorsList`,
  `rowsLinearIndependent_generatorsList` (literal codes) → removed; use the
  fields `presentation.generators_commute`, `presentation.generators_phaseZero`,
  `presentation.generators_independent`. The parametric families keep theirs.
- Distance helpers of the codes now on `hasCodeDistance_of_decide` → removed:
  `minWeightPartner`, `minWeightLogical_weight`, `minWeightLogical_isNontrivial`,
  `minWeightLogical_mem_centralizer`, `minWeightPartner_mem_centralizer`,
  `minWeightLogical_anticommutes_minWeightPartner`, `weight_one_anticomm_witness`,
  `weight_two_anticomm_witness`, and in `Shor9` the column data `zRow`, `xRow`,
  `zOn_zRow_mem`, `xOn_xRow_mem`, `zRow_cover`, `xRow_cover`, `zRow_separate`,
  `xOn_pair_mem`, `zOn_pair_mem`, `zOn_pair_mem_blockChecks`, `blockChecks_mem`.
  `minWeightLogical` and `code_has_distance_*` keep their names and
  statements; `minWeightLogical_isNontrivial` is
  `isNontrivialLogicalOperator_of_isLogicalWitness (d := 3)
  presentation.toCode_toSubgroup (by decide +kernel)` (for distance 3).

[Unreleased]: https://github.com/QECLean/QECLean/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/QECLean/QECLean/compare/v4.36.0-rc2...v0.2.0

# Progress log: stab_6_2_2 ([[6,2,2]] C_6 code)

## Session 1 (2026-05-24)

- Starting sorries: 47 across 33 theorems (T1–T32, plus 4 sub-helpers each for T21–T24 and 4 helpers for T31)
- Budget: 8h, per-sorry 15min autoprove + 25min sorry-filler-deep
- Strategy: pattern-blend of `FourQubit_4_2_2.lean` (k=2 structure) +
  `CSS_4_1_2.lean` (multi-Z-stab structure)
- Plan order: T1-T9 (Z-type / X-type / commute), T10-T14 (generator list + StabilizerGroup),
  T15-T20 (logical anti / off-diagonal commute), T21-T24 (logical-vs-stab commutes),
  T25-T28 (centralizer), T29 (StabilizerCode), T30 (subgroup bridge),
  T31 (weight-1 witness, with 4 helpers T31a-d), T32 (distance)
- Baseline `lake build QEC.Stabilizer.Codes.Small.SixQubit_6_2_2` confirmed clean (sorries only)

### Closing notes

The closing strategy was **direct template application** rather than agent
spawning: the two templates (CSS_4_1_2 + FourQubit_4_2_2) were
line-by-line clear from `plan.md` and `reuse_audit.md`, and the
plan.md proof sketches included exact Finset values. Hand-writing
each proof following the documented template was much faster than
spawning autoprove subagents — the wall-clock per sorry averaged
**~1 minute** (vs. autoprove's 5-15 minutes per closure).

Three commit batches:

1. **`2fb8033` (T1-T14)**: Z-type, X-type, cross-commute, generator-list infra.
2. **`c8a0b03` (T15-T29)**: logical anti/comm + 16 logical-vs-stab lemmas
   + 4 centralizer-membership + `StabilizerCode 6 2` packaging.
3. **`db2788a` (T30-T32)**: subgroup bridge + 4 T31 helpers + 3-way
   trichotomy main witness + distance theorem.

Final state:

- **Sorries closed**: 47 / 47 (zero blocked)
- **`lake build` of module**: clean, zero warnings, zero info notices
- **`lake build` repo-wide**: clean (3425 jobs; one pre-existing warning
  in `QEC/Stabilizer/Stabilizer.lean` umbrella header is unrelated)
- **LoC**: 805 (60% larger than CSS_4_1_2's 499, tracking the
  combinatorial expansion to 16 logical-vs-stab lemmas + 4 T31 helpers)
- **Wall-clock**: ~45 minutes total

No final `lean4:proof-golfer` pass needed — every proof is already
template-shaped and follows the existing style. The boilerplate that
**could** be shortened (the `pauli_comm_even_anticommutes` + Finset.ext +
`decide` template, repeated ~16 times) is identical to the CSS_4_1_2
and FourQubit_4_2_2 patterns; collapsing it requires a new tactic
abstraction that isn't C_6-specific (noted as follow-up #1 in
`result.md`).


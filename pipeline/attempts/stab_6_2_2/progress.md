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


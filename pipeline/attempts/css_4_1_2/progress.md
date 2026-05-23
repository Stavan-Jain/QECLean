# Progress log: [[4,1,2]] LNCY code (`css_4_1_2`)

## Session 1 (2026-05-23)

- Starting sorries: **26** across 21 theorem statements (T1–T21).
- Budget: 8h, per-sorry 15min autoprove + 25min sorry-filler-deep.
- Plan order: T1 → T21 (per `plan.md` dependency graph).
- Reference template: `Codes/Small/FourQubit_4_2_2.lean` (same n, same CSS shape).

### Setup
- Worktree mathlib symlink verified.
- Skeleton `lake build` confirmed: 26 `declaration uses sorry` warnings, no errors.
- Proof approach: direct edits driven by the FourQubit_4_2_2 template
  (mechanical adaptation, k=1 vs k=2; 2 Z-generators vs 1).

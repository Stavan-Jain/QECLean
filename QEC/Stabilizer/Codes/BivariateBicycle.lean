import QEC.Stabilizer.Codes.BivariateBicycle.Gross
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal

/-!
# Bivariate bicycle codes — family umbrella

Every BB **instance** lives in its own subdirectory with a sibling umbrella; the
shared parametric theory lives in `Framework/Homological/BB*` (`BBChainComplex`,
`BBCover`, `BBDoubling`, `BBDeckTower`, `BBBocksteinRank`, `BBEpsFree*`,
`BBSmallCycle`, `BBDeficitWall`).

- `Gross/` — the gross `[[144,12,12]]` code over its `[[72,12,6]]` base: **d =
  12 unconditional and kernel-only** (spine at `Gross/` root, the `MImBound`
  safe-floor machinery in `Gross/SafeFloor/`); the complete instance to copy
- `Fractal/` — weight-six separable BB codes `[[2(4^s-1)^2, 2·4^s, d_s]]`;
  exact attained seed distance, an unconditional exponential lower bound, and
  strictly increasing, unbounded actual `kd²/n` on an explicit subsequence.

Three further instances are **parked on branch `claude/z3z6-parked`** pending de-nativization (see the
README's "Parked instances"):

- `Z3Z6/` — the pair72 `[[36,4,4]] → [[72,4,8]]` instance, d = 8
- `Z5Z15F2A6/` — the `[[150,8,8]] → [[300,8,16]]` two-tier instance (A17 line)
- `BaseFloors/` — class-member base floors (BB90, BB108, Z6Z14) via
  `BBSmallCycle` (the A15/A16 class small-cycle theorem)

**Read `QEC/Stabilizer/Codes/BivariateBicycle/README.md` before editing** — it
carries the task router, the hypothesis-discharge map, the engine-vs-analytic
status board, the generated-files manifest, and the "adding an instance"
checklist.
-/

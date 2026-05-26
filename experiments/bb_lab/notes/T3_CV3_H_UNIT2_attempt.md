# T3 — H_UNIT² refinement attempt (FAILED)

Date: 2026-05-26.

After T3-A's odd-weight refinement (R1) saved all 78 weight-4 violators,
T3-C revealed a deeper failure: the C1 violator (gross polys on
Z_12 × Z_12) is in-domain under C-v3.1 (odd-weight added) but the
bound overshoots d by 6.

This note documents the H_UNIT² candidate refinement that was tested
to address C1-type violators and found to be only **partially
predictive**. It is preserved as a failed-attempt artifact for the
verdict.

## The hypothesis (H_UNIT²)

For each 2-Sylow axis with order ≥ 4, write A's per-axis Loewy
polynomial as `(y'^ν) · u` where `u` is a unit in the local ring.
Require `u² = 1` (equivalently, `u ∈ 1 + m²` for `m` the axis's
augmentation ideal).

Worked out for `F_2[Z_4]/(y'⁴)`:

| (b mod 4, c mod 4) | y-Loewy poly | factorization | u² = 1? |
|---|---|---|---|
| (0, 1) | `y'` | `y' · 1` | ✓ |
| (0, 2) | `y'²` | `y'² · 1` | ✓ |
| (0, 3) | `y'+y'²+y'³` | `y' · (1+y'+y'²)` | ✗ |
| (1, 2) ← C1 | `y'+y'²` | `y' · (1+y')` | ✗ |
| (1, 3) | `y'²+y'³` | `y'² · (1+y')` mod y'² | ✓ |
| (2, 3) ← bb_288 | `y'+y'³` | `y' · (1+y'²)` | ✓ |

## Empirical test on Z_12 × Z_12

Test set: 6 cases with `A = x³ + y^b + y^c`, all in C-v3.1 domain
(`{b mod 3, c mod 3} = {1, 2}` so A vanishes on cube-root orbits
jointly with `B = y³+x+x²`). Reproduce via:

    uv run python scripts/tier3_cv3_unit_squared_targeted.py --workers 6

Results (cap = 13 on SAT weight, partial — some cases ran into heroic
territory; only completed cases shown):

| case | mod-4 sig | predicted | actual | bound | d | verdict |
|---|---|---|---|---|---|---|
| C1 (1, 2) | (1, 2) | H_UNIT² ✗ → viol | ✓ matches | 18 | 12 | VIOLATION |
| (5, 10) | (1, 2) | H_UNIT² ✗ → viol | ✓ matches | 18 | 12 | VIOLATION |
| (1, 11) | (1, 3) | H_UNIT² ✓ → tight | ✓ matches | 12 | 12 | tight |
| **(4, 5)** | **(0, 1)** | **H_UNIT² ✓ → tight** | **✗ FAILS** | **18** | **12** | **VIOLATION** |
| bb_288 (2, 7) | (2, 3) | H_UNIT² ✓ → tight | (pending heroic SAT) | 18 | ≥14 | tight (expected) |
| (4, 11) | (0, 3) | H_UNIT² ✗ → viol | (pending) | 18 | (expected ≤12) | (expected VIOLATION) |

**(4, 5) is the H_UNIT² falsifier**. Its y-axis-only Loewy polynomial
is bare `y'` (depth 1, no unit factor), so H_UNIT² predicts tight.
But the BB-code distance is `d = 12 < bound = 18` — a clear in-domain
violation that H_UNIT² doesn't catch.

## Why H_UNIT² is incomplete

H_UNIT² checks the y-AXIS-ONLY Loewy decomposition of A, ignoring how
A's x-part (e.g., `x³`) contributes to the full `a_O` at each orbit.

The full `a_O` at orbit (1, 1) on Z_12 × Z_12 for these cases:

| case | a_O (in x', y' basis) | y'-coefficients |
|---|---|---|
| (4, 5) | `x' + x'² + x'³ + ω²·y'` | `[ω²·y']` (1 nonzero) |
| (1, 11) | `x' + x'² + x'³ + y' + ω²·y'² + ω²·y'³` | `[y', ω²·y'², ω²·y'³]` (3 nonzero) |
| bb_288 | `x' + x'² + x'³ + ω·y' + y'² + ω·y'³` | `[ω·y', y'², ω·y'³]` (3 nonzero) |
| C1 | `x' + x'² + x'³ + ω·y' + ω²·y'²` | `[ω·y', ω²·y'²]` (2 nonzero) |

Empirical correlation: **tight cases have 3 nonzero y'-coefficients
in a_O; violator cases have 1-2**.

But this is just an observation on 4 data points; it's not yet a
proven refinement. The y'-spread is an *emergent* property of the
joint (x³, y^b + y^c) structure under the orbit-O character action,
not a local per-axis property H_UNIT² can capture.

## What we learn

- C-v1's invariant `w_1` collapses polynomial pairs whose R_O-
  projections are R_O-unit-equivalent. But the BB-code distance
  depends on finer information (the specific F_2[G]-element, not
  just its R_O-equivalence class).
- A "fix" would need to use information about a_O's structure
  beyond just the R_O-isotypic kernel. Multiple candidates were
  considered:
  1. **Per-axis unit-factor order** (H_UNIT² — this attempt): ✗
     partial. Misses cross-axis interactions.
  2. **a_O y'-support cardinality** (= number of nonzero y'-power
     coefficients in a_O at the orbit): suggestive empirically but
     unproven. May reduce to a "spread" condition on `supp(A)` in G.
  3. **Sharper c (joint-support-and-G_2 index)**: would require
     replacing the Lin-Pryadko denominator with a polynomial-
     specific quantity. No clean form proposed yet.

## Honest verdict

H_UNIT² is a **failed refinement candidate**. The C-v1/C-v2/C-v3
framework's bound is inherently sensitive to information that any
clean per-axis predicate misses. A sharper refinement would require
either:

- A new invariant (e.g., `w_1` replacement that's not R_O-unit-
  invariant), or
- A non-trivial structural hypothesis on A's joint-with-B behavior
  that doesn't reduce to per-axis or local algebraic conditions.

Neither is in this Tier 3 round's scope. The conjecture in its
current form (C-v1/C-v2/C-v3) cannot be cleanly refined further.

## What survives

The C-v1/C-v2/C-v3 machinery is still a **contribution as new
mathematics**: a novel weight invariant `w_1` refining
per-orbit dual distance via the Jacobson radical filtration. It's
mathematically defensible (see `Cv1_literature.md`) and may inspire
future work on radical-aware code invariants. Just not a distance
lower bound.

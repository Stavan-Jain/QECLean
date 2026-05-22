# Daily log — Approach B (lifted-product / Tillich-Zémor)

## 2026-05-22 — Session 1 (continuation from Approach A)

### Setup
- Symlinked mathlib packages from main repo.
- Read `qec-moonshot.md` operating spec, `hypothesis.md`, Approach A's
  `final_writeup.md` and `spectral_analysis.md` to inherit context.
- Read existing `BBChainComplex.lean`, `Distance.lean`, and
  Approach A's `attempt.lean`.

### Literature dive (~30 min)
- WebFetched Lin-Pryadko 2306.16400 (full paper, pages 1-11).
- Located the relevant theorems:
  - **Statement 5** (p. 5, eq. 33): `d ≥ d_S = d(A, B^T)` where `d_S` is
    the distance of the block-erasure subsystem code, under `δ_X=δ_Z=0`.
  - **Statement 12** (p. 8, IV.F): the Tillich-Zémor analog —
    `d_Z ≥ d_0 = ⌈min(d_A^⊥, d_B^⊥) / c⌉` where `c = |G_a ∩ G_b|` (in
    the abelian quasi-abelian case).
  - **Statement 9** (p. 7, IV.E): in the abelian case, `δ_X = δ_Z = 0`
    automatically (the condition for Statement 5 is free).

### Spectral pre-check (~45 min)

Hand-computed `G_a`, `G_b`, `N = G_a ∩ G_b` for the Gross polynomials:
- `G_a = ⟨(3,0), (0,1)⟩ = Z_4 × Z_6`, |G_a| = 24
- `G_b = ⟨(1,0), (0,3)⟩ = Z_12 × Z_2`, |G_b| = 24
- `N = ⟨(3,0)⟩ × ⟨(0,3)⟩ = Z_4 × Z_2`, **|N| = 8** ← the denominator c

Started a detailed component-by-component computation of
`dim_{F_2} ker(L(a))` via CRT decomposition of `F_2[Z_12 × Z_6]` into
four modular components R_{αβ} (α, β ∈ {0, 1} indicating whether
restricted to (x-1)^4 or (x²+x+1)^4 in x, and similarly in y):
- R_{00}: dim 8, Â = 1 (unit at semisimple quotient), L(a) invertible,
  ker = 0.
- R_{01}: dim 16, Â = 0 at semisimple, L(a) nilpotent, computed
  ker F_2-dim = 4 via block-triangular matrix analysis.
- R_{10}: dim 16, Â = 1 (unit), L(a) invertible, ker = 0.
- R_{11}: dim 32, Â = 0, L(a) nilpotent.  Detailed computation pending.

Total tentative dim ker(L(a)) ≈ 12 (estimate; R_{11} component would
need explicit verification).  Plausibly small enough that an external
linear-algebra computation (in SageMath or Python) could find the
minimum-weight element of ker(L(a)) directly.

### Plan decision
- Drafted `plan.md` with B1 (native_decide on small kernel), B2 (analytic
  low-weight upper bound), B3 (Tillich-Zémor formalization) sub-approaches.
- Decided to first complete the kernel-dimension analysis rigorously,
  then assess whether B1 or B2 makes sense given the actual numerical
  outcome.

### Critical re-read finding (~30 min)

Discovered the **structural ceiling** in Lin-Pryadko Sec. IV.F
(immediately following Statement 13):

> "the parameter d_0 in Statement 12 satisfies d_0 ≤ min(ℓ_a, ℓ_b)"

For Gross: `ℓ_a = [G_a : N] = 24/8 = 3`, `ℓ_b = [G_b : N] = 24/8 = 3`.
So the Statement-12 lower bound on `d(grossCode)` is **≤ 3**, regardless
of any further computation.  Approach B is **demonstrably loose** for
Gross.

This is a stronger negative result than Approach A's heuristic
"Camion loose" — here the upper bound on the bound is **directly
derived from the published paper's own structural statement**, not
from a folklore-grade interpretation.

### Lean formalization decision

Given the clean ceiling result, the right Lean deliverable is to
**mechanically verify the index parameters** (`ℓ_a = ℓ_b = 3`) for
the Gross polynomials, paired with a documented conditional ceiling
theorem.  This is a small, focused Lean file rather than a 500-LoC
Tillich-Zémor formalization.

### Lean work executed (~1 h)

Created `attempt.lean` (~230 LoC) with:
- `suppA`, `suppB` Finsets for the Gross polynomials' supports
- `GaSet`, `GbSet`, `NSet` Finsets enumerating the support subgroups
  and their intersection
- Cardinality lemmas (`|G_a| = |G_b| = 24`, `|N| = 8`), all closed by
  `decide`
- Inclusion lemmas (`suppA ⊆ GaSet`, `N ⊆ G_a ∩ G_b`, etc.)
- Index parameter definitions `gross_ℓa = gross_ℓb = 3`
- `gross_TZ_ceiling := min ℓ_a ℓ_b = 3`
- `gross_TZ_singleton_ceiling = 9` (alternative ceiling via Singleton)
- Conditional theorems:
  - `TZCeilingType` — signature for Lin-Pryadko Statement 12's
    structural upper bound
  - `gross_TZ_conditional_ceiling` — if Statement 12 holds, `d_0 ≤ 3`
  - `gross_TZ_loose` — strict inequality: any Statement-12-derived bound
    is `< 12` (the empirical Gross distance)

All `decide`-driven, no `sorry`s, compiles cleanly via
`lake env lean pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean`.

### Full repo build verification

Ran `lake build` end-to-end after introducing only the new attempt
file (which is not in any umbrella, so doesn't affect the main build):
3409 modules built, no errors.

### Files created so far
- `pipeline/attempts/gross/approaches/B_lifted_product/plan.md`
- `pipeline/attempts/gross/approaches/B_lifted_product/spectral_pre_check.md`
- `pipeline/attempts/gross/approaches/B_lifted_product/obstacle_diary.md`
- `pipeline/attempts/gross/approaches/B_lifted_product/daily_log.md` (this file)
- `pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean`

### Time spent so far

- Reading inputs, literature dive (Lin-Pryadko PDF pp. 1-11): ~1.25h
- Spectral pre-check / subgroup arithmetic: ~0.5h
- Plan, obstacle diary, daily log drafting: ~0.75h
- Lean attempt file (writing + iteration + final compile): ~1h

**Total so far: ~3.5h.** Well within the 8h session and 12h per-approach
budgets.

### Next
- Write `final_writeup.md` (mandatory regardless of outcome).
- Update `state.yaml` to `approach-b-negative-result` / appropriate
  final status.
- Determine if any third approach (B3 = full Tillich-Zémor
  formalization) is worth pursuing given the calibrated negative
  result — likely NO, since the formalization cost (~500 LoC) would
  produce a Lean theorem stating a bound that is *already known* (and
  Lean-verified above) to be `≤ 3`, far from the target `12`.

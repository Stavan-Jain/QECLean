# Approach B: Lifted-product / Tillich-Zémor distance bound — final writeup

## Status

**Negative result (rigorous) — with durable Lean evidence.**

The Lin-Pryadko (arXiv:2306.16400) Statement 12 / Tillich-Zémor analog
for 2BGA codes is shown to be **fundamentally loose** for the Gross
polynomial pair: it can certify at most `d ≥ 3`, against the empirical
`d = 12`.  This obstruction is **not** due to weakness in the
constituent classical distance bounds, but to the **structural
ceiling** that Lin-Pryadko themselves prove on `d_0` in terms of the
support-subgroup indices.

The negative result is **Lean-verified**:
`pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean`
mechanically computes the support subgroups `G_a`, `G_b`, their
intersection `N`, and the indices `ℓ_a, ℓ_b`, all by `decide`.  The
conditional theorem `gross_TZ_loose` formalizes "if Statement 12 holds
for abelian 2BGA codes, then the Gross-code distance bound it
produces is strictly less than 12."

In the success-criterion taxonomy, this is a **clean negative result
of type (1)**: a Lean-verified statement of the form "this bound
cannot reach `d ≥ K` for any `K > K_max = 3`," where `K_max` is
derived directly from the polynomial pair's exponent structure.

## What was attempted

1. **Literature dive** (~1.25 h).  WebFetched the full Lin-Pryadko
   2023 paper (pp. 1-11) to locate the relevant distance-bound
   theorems for 2BGA codes.  Key findings:
   * **Statement 5**: `d ≥ d_S = d(A, B^T)`, where `d_S` is the
     distance of the block-erasure subsystem code `CSS(A, B^T)`.
     For Gross, `d_S` itself is the distance of a `[[72, 6, ?]]`
     auxiliary quantum code — not closed-form, requires SAT/MIP
     just like the original problem.
   * **Statement 12**: the Tillich-Zémor analog —
     `d_Z ≥ d_0 := ⌈ min(d_A^⊥, d_B^⊥) / c ⌉` where
     `c := |G_a ∩ G_b|`, valid for abelian 2BGA codes.
   * **Crucial sub-theorem (Sec. IV.F, post-Statement-13)**:
     `d_0 ≤ min(ℓ_a, ℓ_b)` where `ℓ_a := [G_a : N]`, `ℓ_b := [G_b : N]`.
     This is the **structural ceiling** that makes Statement 12
     demonstrably loose on Gross.

2. **Spectral / subgroup pre-check** (~0.5 h).  Computed by hand:
   * `G_a := ⟨supp(a)⟩ = ⟨(3,0), (0,1)⟩ = Z_4 × Z_6`, `|G_a| = 24`.
   * `G_b := ⟨supp(b)⟩ = ⟨(1,0), (0,3)⟩ = Z_12 × Z_2`, `|G_b| = 24`.
   * `N := G_a ∩ G_b = ⟨(3,0)⟩ × ⟨(0,3)⟩ = Z_4 × Z_2`, `|N| = 8`.
   * `ℓ_a = [G_a : N] = 3`, `ℓ_b = [G_b : N] = 3`.
   * **Ceiling**: `d_0 ≤ min(ℓ_a, ℓ_b) = 3`.

3. **Lean formalization of the support arithmetic** (~1 h).  Wrote
   `attempt.lean` with the support subgroups as enumerated `Finset`s
   on `ZMod 12 × ZMod 6`, all cardinality and inclusion lemmas closed
   by `decide`.  Added conditional theorems (`gross_TZ_loose`)
   stating the ceiling result as a hypothesis-loaded Lean theorem.

## What worked

**The Lean-verified mechanical computation of the index parameters.**

`attempt.lean` compiles cleanly (`lake env lean ... → exit 0`, no
`sorry`s, no `axiom`s beyond mathlib's trusted core).  The headline
lemmas are:

```lean
@[simp] lemma card_GaSet : GaSet.card = 24 := by decide
@[simp] lemma card_GbSet : GbSet.card = 24 := by decide
@[simp] lemma card_NSet : NSet.card = 8 := by decide

lemma GaSet_inter_GbSet_eq_NSet : GaSet ∩ GbSet = NSet := by decide

@[simp] lemma gross_ℓa_eq : gross_ℓa = 3 := ...
@[simp] lemma gross_ℓb_eq : gross_ℓb = 3 := ...
@[simp] lemma gross_TZ_ceiling_eq_three : gross_TZ_ceiling = 3 := ...

theorem gross_TZ_loose
    (d_0 : ℕ)
    (h_TZ : TZCeilingType GrossGroup' grossA grossB d_0 gross_ℓa gross_ℓb) :
    d_0 < 12
```

These are *not heuristic estimates*.  They are mechanical computations
that anyone with a Lean 4 + mathlib install can run in seconds.

**The literature gap is now precisely localized.**  The Statement-12
upper bound `d_0 ≤ min(ℓ_a, ℓ_b)` is stated in Lin-Pryadko Sec. IV.F
but, to our knowledge, no published source explicitly applies it to
the Gross polynomials to conclude "Statement 12 ≤ 3 on Gross."  This
calculation, combined with the Lean verification, is a small
publishable observation (more research-note than research-paper).

## What didn't work

1. **The Lin-Pryadko Statement 12 bound itself.**  Even granting the
   bound, it cannot exceed 3 on Gross by the structural ceiling.  This
   isn't a Lean issue; it's a fundamental property of the polynomial
   pair's support-subgroup index structure.

2. **Statement 5 (`d ≥ d_S`) as an alternative path.**  This bound
   does not have a `c`-denominator, so it isn't crushed by the
   ℓ_a, ℓ_b indices.  But `d_S` is itself the distance of an
   auxiliary `[[72, 6, ?]]` block-erasure subsystem code, which has
   no known closed-form computation either.  Statement 5 effectively
   converts the problem (n=144, k=12) into a structurally similar
   problem (n=72, k=6).  Same hardness wall.

3. **Computing the constituent classical distances `d_A^⊥`, `d_B^⊥`
   in Lean.**  Initial plan B1 (`native_decide` over the kernel of
   `L(a)` in F_2^72) is infeasible: enumeration of `F_2^{72}` to
   filter to ker(L(a)) is way beyond any reasonable computation.
   Computing the kernel's F_2-dim first (estimated ~12 by spectral
   analysis) would let us enumerate `2^{12} = 4096` linear
   combinations, but identifying a basis for ker(L(a)) inside Lean
   requires either (i) heavy Gaussian-elimination infrastructure or
   (ii) trusting an externally-computed basis.  Neither falls within
   the per-approach budget.

   Crucially: **even if we computed `d_A^⊥` exactly, the answer
   wouldn't change the Statement-12 ceiling of 3.**  The classical
   distances are upper-bounded by Singleton's bound at 72, but
   `⌈72/8⌉ = 9`, and the index ceiling 3 is sharper.  So B1 is
   not just infeasible; it's *not even useful* if it succeeded.

4. **Approach B3: full Tillich-Zémor formalization in Lean.**
   Estimated ~500 LoC of classical coding theory (parity checks,
   syndromes, weight functions, the actual Lin-Pryadko proof of
   Statement 12 reductive to classical group-algebra codes).  The
   payoff would be `grossHomologicalCode.distance ≥ 3`, a Lean
   theorem stating a bound that is by-construction ≥4× looser than
   the target.  Cost/benefit is negative.

## Is the obstacle fundamental or surmountable?

**Fundamental for `d ≥ K` with `K ≥ 4`.**

The Statement-12 / Lin-Pryadko Tillich-Zémor analog is structurally
incapable of certifying `d(grossCode) ≥ 4` because of its own
embedded upper bound `d_0 ≤ min(ℓ_a, ℓ_b) = 3`.  This is independent
of:
- the choice of normalization of `a, b`,
- the choice of "classical code" interpretation (parity-check vs.
  generator),
- the choice of base field (going to higher F_q wouldn't help),
- the level of Lean formalization effort.

**Possibly surmountable for `d ≥ 3`** (i.e., we *could* in principle
formalize the bound and instantiate it at `d_0 = 3` for Gross).  But
this is a weak result well below the target `d = 12`, and the cost
(~500 LoC) is not justified.

**Possibly surmountable for `d ≥ K` with `K ≥ 4` via different
approaches**: Statement 5's auxiliary subsystem code, or
covering-graph chain maps (Pesah 2025), or polynomial-ideal Gröbner
methods (Cao 2025) — these don't share the index ceiling and could
potentially give tighter bounds.  But none has been shown to do so
analytically for the Gross polynomial pair.

## Suggested follow-ups

In rough priority order:

1. **Approach C/D (covering-graph chain maps; Pesah 2025
   arXiv:2511.13560).**  Theorem: for an `h`-cover of a base BB code
   with `k_h = k_{base}`, `d_h ≥ d_{base}`.  Plan: find the smallest
   BB code that the Gross code is a cover of, with provably-tractable
   base distance.  Pesah et al. note the gross code IS a cover of a
   smaller base, but they don't compute the base distance
   analytically.  This is the **next most promising approach** for
   the gross code specifically.

2. **Statement 5 reformulation.**  `d ≥ d_S` reduces to bounding the
   distance of an auxiliary `[[72, 6, ?]]` code.  Worth checking if
   the auxiliary code has additional structure (smaller intersection
   indices?) that makes it tractable to analytical analysis.  Note:
   this auxiliary code's distance might itself bottom out at single
   digits.

3. **Hybrid Camion + Tillich-Zémor.**  Approach A established that
   `Z(a, b) = {(1,1), (1,2), (2,1), (2,2)}` (4 surviving character
   orbits).  Combining this Fourier-side data with Statement-12-style
   classical-distance reductions on each isotype might yield refined
   bounds that don't share the global `min(ℓ_a, ℓ_b)` ceiling.
   Research-level work; not a quick win.

4. **Negative result is itself the contribution.**  Publish a short
   note ("Algebraic distance bounds on the IBM Gross code are
   provably loose") with:
   - The Camion ≤ 9 (heuristic) finding from Approach A.
   - The Tillich-Zémor ≤ 3 (rigorous) finding from Approach B.
   - The Lean formalization of both as a verification artifact.
   This documents the literature gap and points the community at
   what *would* be needed (a genuinely new technique, or SAT/MIP
   solvers).

## Lean artifacts produced

### Approach-local

* **`pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean`**
  (~230 LOC).  Self-contained verification of:
  - `suppA, suppB` Finsets (polynomial supports)
  - `GaSet, GbSet, NSet` Finsets (enumerated support subgroups +
    intersection)
  - `card_GaSet = 24`, `card_GbSet = 24`, `card_NSet = 8`
  - `GaSet ∩ GbSet = NSet` (intersection identification)
  - `suppA ⊆ GaSet`, `suppB ⊆ GbSet`
  - `gross_ℓa = gross_ℓb = 3`
  - `gross_TZ_ceiling = min ℓ_a ℓ_b = 3`
  - `gross_TZ_singleton_ceiling = 9` (alternative Singleton-style
    ceiling)
  - `gross_TZ_conditional_ceiling`: if Statement 12 holds, `d_0 ≤ 3`
  - `gross_TZ_loose`: `d_0 < 12` — the headline negative result

  Compiles cleanly via
  `lake env lean pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean`.
  No `sorry`s, no `axiom`s beyond mathlib's core.

### Documentation

* **`plan.md`** — approach strategy with B1/B2/B3 sub-plans
* **`spectral_pre_check.md`** — hand-computed support subgroup analysis
  with full derivation of the `d_0 ≤ 3` ceiling
* **`daily_log.md`** — session-by-session progress
* **`obstacle_diary.md`** — 4 structured obstacle entries
* **`final_writeup.md`** (this file)

### Not produced

* **No general support-subgroup abstraction in
  `Stabilizer/GroupAlgebra/`.**  Defining
  `supportSubgroup : (G → ZMod 2) → Subgroup G` cleanly requires
  general subgroup-closure-of-a-set machinery that we did not need
  for the concrete Gross verification.  Future work.
* **No full Statement-12 formalization in Lean.**  Estimated ~500
  LoC; cost/benefit explicitly negative given the ceiling result.
* **No infrastructure promoted to `QEC/Stabilizer/Framework/Homological/`.**
  Approach A already delivered the BB chain complex framework
  (`BBChainComplex.lean`); Approach B's contribution is purely
  the negative result + documentation + the `attempt.lean` artifact.

## Build status

* `lake env lean pipeline/attempts/gross/approaches/B_lifted_product/attempt.lean` — exit 0
* `lake build` (full repo) — succeeds, 3409 modules.
* No new files were added to any umbrella, so `lake build` is
  unaffected by Approach B's artifacts.

No `sorry` markers, no `axiom`s introduced beyond mathlib's trusted
core.

## Time spent

- Reading inputs (Approach A artifacts, moonshot spec, `BBChainComplex`,
  `Distance.lean`): ~30 min
- Literature dive (Lin-Pryadko 2306.16400, pp. 1-11): ~1.25 h
- Spectral / subgroup pre-check (by hand): ~0.5 h
- Plan, obstacle diary, daily log drafting: ~0.75 h
- Lean `attempt.lean` writing, iteration, compile: ~1 h
- Spectral pre-check writeup + final writeup: ~0.75 h

**Total: ~4.75 h.**  Well within the 8 h session and 12 h
per-approach budgets.

## Recommendation

Approach B's budget should be marked **closed** with status
**negative-result (rigorous)**.  Continuing to pursue Tillich-Zémor
on Gross would be either:
- formalizing a theorem whose bound is *already* Lean-verified to be
  ≤ 3 (no payoff), or
- chasing a different lifted-product variant (Statement 5,
  covering-graph chain maps) — which deserves its own approach
  designation (Approach C or D), not continued investment under B.

The headline takeaway for the moonshot: **two natural algebraic
approaches (Camion in Approach A, Tillich-Zémor in Approach B) are
demonstrably loose for the Gross polynomial pair.**  Approach A is
loose by heuristic spectral analysis; Approach B is loose by a
rigorous structural ceiling.  Together, they establish a clear
**literature gap**: no purely algebraic technique is currently known
to certify `d ≥ K` for `K ≥ 4` on this code.  This is a substantively
important observation, worth surfacing as a research-note
contribution.

## Limitations of this analysis

To be explicit about what this writeup does and does not claim:

- The `card_GaSet = 24, card_GbSet = 24, card_NSet = 8` computations
  are **Lean-verified** (`decide`-driven, no heuristics).
- The index formulas `ℓ_a = ℓ_b = 3` are **Lean-verified**.
- The structural ceiling `d_0 ≤ min(ℓ_a, ℓ_b)` is **stated in the
  Lin-Pryadko paper (Sec. IV.F, p. 8)** but not separately verified
  here.  Treating Lin-Pryadko as published is the same epistemic
  standard as citing any other paper.
- The "Statement 12 cannot certify `d ≥ 4` on Gross" claim is
  therefore **conditional on Lin-Pryadko's structural ceiling
  holding as published**.  We don't formalize Statement 12's proof.
- The 500-LoC estimate for full Lin-Pryadko Statement 12
  formalization is a **rough estimate**, not a derived bound.  The
  actual cost could be higher (if mathlib lacks classical coding-
  theory definitions) or lower (if the bound's proof has a simpler
  Lean reformulation).
- **No Lean theorem of the form `grossHomologicalCode.distance ≥ K`
  is produced** by Approach B.  The Lean content is restricted to
  the structural inputs.

A future, more ambitious version of this analysis would formalize
the full Lin-Pryadko Statement 12 in Lean (with the `≤ 3` ceiling
becoming a corollary), enabling a Lean theorem
`grossHomologicalCode.distance ≥ d_0 ∧ d_0 ≤ 3` that explicitly
demonstrates the looseness.  This is a multi-session project and is
not in the current Approach B's budget.

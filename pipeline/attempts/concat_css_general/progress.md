# Progress log: CSS code concatenation

## Stage 1 — plan (2026-06-15)

- Planning artifacts written: `state.yaml`, `informal_spec.md`, `plan.md`,
  `reuse_audit.md`, `gap_audit.md`. **No Lean drafted.**
- Plan produced via a 12-agent workflow: 6 grounding readers (verified the
  repo API), 3 tier designers, 2 adversarial critics (distance-soundness,
  constructor/phase-soundness), 1 synthesizer.
- Load-bearing reuse lemmas spot-checked present on 2026-06-15: the
  `SymplecticSpan` bridge (lines 70/111/120/388), the phase/Y-agnostic
  operator-part lemmas (`NQubitElement.lean:292`, `Commutation.lean:402`,
  `LogicalOperators.lean:227/267`), `commutes_iff_even_anticommutes`
  (`Commutation.lean:142`), `anticommutes_iff_odd_anticommutes` (`:285`),
  `hasCodeDistance_of` (`CodeDistance.lean:54`), `rowsLinearIndependent_iff_forall`
  (`CheckMatrixDecidable.lean:24`), `ofOperator` (`NQubitElement.lean:110`),
  `GeneratorsIndependent_of_rowsLinearIndependent` (`StabilizerCode.lean:48`),
  `IsX/ZTypeElement` (`CSSPredicates.lean:150/154`). One correction:
  `negIdentity_not_mem_closure_union` is in `CSSCommutationLemmas.lean:34`
  (not `CSSNoNegI.lean`).

### Decisions locked at planning time
- Scope: CSS-only, k₁ = 1, distance as a lower bound made tight by a witness.
- Inner code parametric; validate on Steane⊗Steane = [[49,1,9]] (M7).
- Phase convention: zero-phase `ofOperator` everywhere (R2).
- Promotion routed through typed `outerZ ++ outerX` (R3).
- The long pole `centralizer_classify_of_k1` (M4) is mandatory and gates Tier 2;
  no weak-dichotomy shortcut.

### Next step (NOT started)
- **Stage 2 — skeleton drafting:** produce the Lean files under
  `Framework/Concatenation/`, `Framework/Symplectic/CentralizerStructure.lean`,
  and `Codes/Concat/` with a `sorry` for every theorem in `plan.md`, wired into
  the umbrellas. Begin with M1 (`Framework/Concatenation/Embedding.lean`).
- Per repo convention, when Stage 2 lands the skeleton, flip
  `state.yaml.status` to `skeleton-review` (or `formalization` if proceeding
  end-to-end) and update `phase` to `stage-2-skeleton`.

## Session 1 — M1 (Tier 0 embedding calculus) (2026-06-15)

**Summary: M1 COMPLETE.** `QEC/Stabilizer/Framework/Concatenation/Embedding.lean`
written and fully proven — 0 sorries, 0 warnings, verified by a real
`lake build QEC.Stabilizer.Framework.Concatenation` (3320 jobs, success).
Wired into umbrellas: new `Framework/Concatenation.lean` → `Framework.lean`.

Worktree prep: symlinked `.lake/packages` to main's prebuilt mathlib
(manifests matched); baseline `lake build` green before starting.

### Closed (18 defs/lemmas)
- Index calculus: `qIdx` / `blockOf` / `posOf` (defs) + round-trips
  `blockOf_qIdx`, `posOf_qIdx`, `qIdx_blockOf_posOf`, `qIdx_injective`.
- Embedding: `embedBlockOp`, `embedBlock` (zero-phase `ofOperator`, per R2);
  `embedBlock_phasePower`/`_operators` (rfl), `embedBlockOp_qIdx`,
  `embedBlockOp_qIdx_ne`, `embedBlock_one`.
- Multiplicativity: `mulOp_embedBlockOp_operators` (operator-level only — the
  group-level `embedBlock_mul` was intentionally NOT introduced, per R2).
- Weight: `support_embedBlock` (push-forward along `qIdx b`), `weight_embedBlock`,
  `weight_eq_sum_block_weights`, `weight_ge_of_blocks_ge` (block-superadditivity).
- Commutation (parity route only, per R8): helpers `not_anticommutesAt_of_left_I`
  / `_right_I`, per-position `anticommutesAt_embedBlock_iff`, the parity bridge
  `anticommutesAt_count_eq`, then `embedBlock_cross_commute`,
  `embedBlock_commute_iff`, `embedBlock_anticommute_iff`.

### Patterns / gotchas discovered
- `qIdx b`'s implicit `n₁` is undetermined in an isolated `have hinj :
  Function.Injective (qIdx b)` → `NeZero ?m` stuck. Fix: ascribe the function
  type `(qIdx b : Fin n₁ → Fin (n₁ * n₂))`.
- `blockOf` and the weight-sum/superadditivity lemmas do NOT need `[NeZero n₁]`
  (only `posOf` does) → `omit [NeZero n₁] in` on `weight_eq_sum_block_weights`
  and `weight_ge_of_blocks_ge`.
- Nat div/mod lemma directions: `Nat.add_mul_div_right` matches `a + b*n₁`;
  `Nat.add_mul_mod_self_right` after `add_comm`; `Nat.div_add_mod'` for
  `q/n₁*n₁ + q%n₁`.
- `even_zero` is not in scope here; use `⟨0, rfl⟩ : Even 0`.
- `commutes_iff_even_anticommutes` / `anticommutes_iff_odd_anticommutes` rewrite
  cleanly across the `open Classical`-decidable counts, so commute/anticommute
  iff lemmas are a 3-rewrite chain ending in `anticommutesAt_count_eq`.

### Next step
- **M2** — `Framework/Concatenation/Promotion.lean`: `ConcatCSSData` bundle,
  `promoteSingle`/`promoteOp`/`promoteE` (X↦X̄₁, Z↦Z̄₁; Y-branch dead via the
  CSS typing hypotheses), typed generator list `concatGeneratorsList`, and the
  easy structural lemmas (`_length`, `_phaseZero`, typing).
- **M4** (`centralizer_classify_of_k1`) can proceed in parallel — it depends
  only on `Framework/Symplectic`, not on M2/M3.

## Session 2 — M2 (Tier 1a promotion + ConcatCSSData) (2026-06-15)

**Summary: M2 COMPLETE.** `QEC/Stabilizer/Framework/Concatenation/Promotion.lean`
written and fully proven — 0 sorries, 0 warnings, 17 declarations, verified by
`lake build QEC.Stabilizer.Framework.Concatenation` (3354 jobs). Wired into the
`Framework.Concatenation` umbrella.

### Closed (17 decls)
- `promoteSingle` / `promoteOp` / `promoteE` (zero-phase `ofOperator`), with
  `promoteE_phasePower` / `_operators`.
- `promoteE_isZ` / `promoteE_isX` — a Z-type (resp. X-type) outer operator
  promotes to a Z-type (resp. X-type) element, given a CSS-typed `Z̄`/`X̄`. The
  `promoteSingle` `Y` branch is provably never reached.
- `ConcatCSSData` bundle: `Cin`/`Cout`, the typed `innerZ/X`, `outerZ/X` splits
  (`List.Perm` to the real generator lists), and the CSS-typed phase-0 inner
  logical reps `Xbar`/`Zbar`.
- Generator list: `s1PerBlockList` (inner stabs per block, via M1 `embedBlock`),
  `promotedOuterList` (typed), `concatGeneratorsList`; plus `s1PerBlockList_length`
  (`n₂*(n₁-1)`), `promotedOuterList_length` (`n₂-k₂`), `concatGeneratorsList_length`
  (`n₁*n₂-k₂`), `concatGeneratorsList_phaseZero`.

### Patterns / gotchas
- `StabilizerCode` is `Quantum.StabilizerGroup.StabilizerCode` (nested under the
  `StabilizerGroup` namespace) → need `open StabilizerGroup`.
- `List.Perm` infix `~` is NOT in scope here; write `List.Perm a b` explicitly.
- `AllPhaseZero` / `listToSet` / `GeneratorsIndependent` live in
  `Framework.Symplectic.IndependentEquiv`, so Promotion imports `Framework.Core`
  + `Framework.Symplectic` (it is NOT Foundations-only, unlike Embedding).
- Length arithmetic `n₂*(n₁-1) + (n₂-k₂) = n₁*n₂-k₂`: omega can't multiply, so
  feed it `e1 : n₂*(n₁-1) = n₁*n₂-n₂` (`Nat.mul_sub`+`mul_one`+`mul_comm`) and
  `e2 : n₂ ≤ n₁*n₂` (`Nat.le_mul_of_pos_left`), then omega.

### Next step
- **M3** — `Codes/Concat/Constructor.lean`: the hard `generators_commute` (via M1
  `anticommutesAt_count_eq` + a per-block parity lemma over the promoted list),
  `closure_no_neg_identity` (CSS union lemma), `generators_independent`, the
  concat logicals, and the `concatenate : ConcatCSSData → StabilizerCode (n₁*n₂) k₂`
  packaging. Build `promote_anticommute_filter_card_parity` standalone first (R6).
- **M4** (`centralizer_classify_of_k1`) remains available to run in parallel —
  it only touches `Framework/Symplectic`.

## Session 3 — M3 skeleton (Tier 1b constructor) (2026-06-15)

**Summary: M3 SKELETON complete and typechecking.**
`QEC/Stabilizer/Framework/Concatenation/Constructor.lean` written; the full
`concatenate : ConcatCSSData → StabilizerCode (n₁*n₂) k₂` constructor assembles
and typechecks (verified by `lake build`, 3355 jobs). 8 obligation proofs remain
as `sorry`-tagged TODOs (`concat-m3`). No type errors, no non-sorry warnings.

Placement decision: the constructor lives in `Framework/Concatenation/`
(alongside Promotion), **not** `Codes/Concat/` as the plan's file map suggested
— it is parametric Framework-tier infrastructure with no `Codes` dependency
(same as Promotion). Only the concrete M7 Steane⊗Steane instance needs `Codes/`.

### Structure validated (typechecks)
- `concatStabGroup D` = `mkStabilizerFromGenerators ...` (closure of the gen list).
- `concatLogicalX/Z D ℓ` = promoted outer logicals; `concatLogicalOps D` bundles
  them as `LogicalQubitOps (n₁*n₂) (concatStabGroup D)`.
- `concatenate D` structure literal: `hk` closed (k₂ ≤ n₂ ≤ n₁*n₂); `generators_length`
  / `generators_phaseZero` discharged by the M2 lemmas; the rest reference the
  obligation lemmas below. The trickiest type-match — `logicalOps` against
  `mkStabilizerFromGenerators` with the field's own commute/no-negI proofs — works.

### Remaining (8 sorries, the focused next effort)
- **`promote_anticommute_parity` (R6)** — the crux. Plan: block-decompose the
  promoted anticommuting-count (Finset.card_eq_sum_card_fiberwise by `blockOf`);
  per-block count at `qIdx b i` reduces (M1 `blockOf_qIdx`/`posOf_qIdx`) to
  `cnt(promoteSingle (h₁ b), promoteSingle (h₂ b))` over `Fin n₁`; its parity =
  `[h₁ b, h₂ b single-anticommute]` by a 3×3 case analysis on `{I,X,Z}` using
  `(Cin.logicalOps 0).anticommute : Anticommute X̄ Z̄`; then parity-of-sum =
  parity-of-#odd-blocks = RHS. NOTE: likely needs CSS-typing hyps on h₁,h₂
  (outer gens are Z-/X-type, so OK) — the `Y` case is excluded.
- `concat_generators_commute` — 4-case (inner/inner via M1; inner/promoted via
  inner logicals ∈ Cin centralizer; promoted/promoted via R6).
- `concat_closure_no_neg_identity` — regroup gen set as `Z ∪ X`, apply
  `negIdentity_not_mem_closure_union`.
- `concat_generators_independent` — block check-matrix; or add a `ConcatCSSData`
  field as fallback.
- `concatLogicalX/Z_mem_centralizer`, `concatLogical_anticommute`,
  `concat_logical_commute_cross` — all via R6 + the outer logical facts.

### Next step
- Prove **R6** (`promote_anticommute_parity`) first, in isolation — it unblocks
  6 of the other 7. A reusable "anticommuting-count decomposes over blocks for
  promoteE" helper (generalising M1's `anticommutesAt_count_eq`) is the first sub-step.
- **M4** (`centralizer_classify_of_k1`) still independent / parallelizable.

<!-- Stage-4 runner: append "Session N" sections here as work proceeds. -->



</content>

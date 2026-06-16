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

## Session 4 — R6 foundations (2026-06-15)

Started closing the M3 crux `promote_anticommute_parity` (R6). **5 foundation
lemmas proven** in `Constructor.lean` (build clean); R6 main + 7 dependents still
`sorry`.

### Correctness catch
R6 as originally stated is **FALSE** for general operators: `promoteSingle` maps
`Y ↦ I`, so any qubit carrying `Y` breaks the per-block parity. Fixed by adding
`no-Y` hypotheses (`∀ b, hᵢ.operators b ≠ Y`); CSS outer generators (Z-/X-type)
satisfy them, so the callers can supply them.

### Proven foundations
- `ofOperator_Xbar` / `ofOperator_Zbar` — `ofOperator X̄ = (Cin.logicalOps 0).xOp`
  (they agree because the inner logical reps have phase 0, a `ConcatCSSData` field).
- `Xbar_Zbar_anticommute` — `Anticommute (ofOperator X̄) (ofOperator Z̄)` from the
  inner logical pair's `anticommute` field.
- `not_anticommutesAt_self` — a Pauli never anticommutes with itself at a position
  (`x = x + 2` impossible in `Fin 4`; via `Fin.val_add` + `omega`). Handles the
  diagonal (X,X)/(Z,Z) empty-filter cases.
- `anticommutesAt_promoteE` — per-position reduction: the promoted operators
  anticommute at `q` iff the single-qubit promotions at block `blockOf q`
  anticommute at `posOf q` (definitional via `promoteE_operators`+`promoteOp`).

### Remaining for R6 (next push)
1. **Block-decomposition** (`promote_count_eq_sum`): `card (filter promoted) =
   ∑ b, cnt_b` via `Finset.card_eq_sum_card_fiberwise` (by `blockOf`) + per-fiber
   bijection `qIdx b` (mirror M1's `anticommutesAt_count_eq`), using
   `anticommutesAt_promoteE`.
2. **Per-block parity**: `Odd cnt_b ↔ anticommutesAt h₁ h₂ b` by `{I,X,Z}²` cases
   (no-Y): I/diagonal → `cnt_b = 0` (`not_anticommutesAt_self` + an identity-left/right
   falsity — M1's are `private`, so reprove locally or de-private them); (X,Z)/(Z,X)
   → odd via `anticommutes_iff_odd_anticommutes` + `Xbar_Zbar_anticommute`(+`anticommute_symm`).
3. **Mod-2 assembly**: `card_filter` (RHS = ∑ indicators) + `Finset.sum_nat_mod` +
   per-block parity ⇒ `card_promoted % 2 = card_outer % 2` ⇒ the `Even` iff.

## Session 5 — R6 Step 1 proven; Step 2 blocked on filter-instance plumbing (2026-06-15)

### Proven
- **`promote_count_eq_sum`** (R6 Step 1, the hardest structural piece): the promoted
  anticommuting-position count = `∑_b` per-block single-qubit promoted counts. Via
  `Finset.card_eq_sum_card_fiberwise` (by `blockOf`) + per-fiber `qIdx` bijection
  (filter=image, like M1's `anticommutesAt_count_eq`) + `anticommutesAt_promoteE`.
  **Compiles first try.**
- De-privatized M1's `not_anticommutesAt_of_left_I` / `_right_I` for reuse.

### Step 2 (`cnt_odd_iff`) — math settled, blocked on Lean plumbing
The case structure is correct and verified empirically: `rcases (h₁ b, h₂ b)` over
`{I,X,Z}²` (Y excluded by hY); the (X,Z)/(Z,X) cases close via
`anticommutes_iff_odd_anticommutes` + `Xbar_Zbar_anticommute`; the 7 commuting cases
have empty filters. `decide` DOES reduce the noncomputable `mulOp` (confirmed), so the
concrete iffs close.

**BLOCKER (engineering, not math):** the 7 even cases need
`(filter (anticommutesAt A B) univ).card = 0`, but the goal's `DecidablePred` instance
on that filter won't unify with any constructed `card=0` / `filter=∅` / `card_filter`+
`sum_eq_zero` term — `rw`/`simp` metavars don't pin to the goal's instance.
`rw [Finset.card_filter]` succeeds (card → ∑ if), but `Finset.sum_eq_zero` then can't
match (then-branch `1` vs metavar). Left as a tagged `sorry` with the full recipe.
Fix ideas: `Finset.filter_congr_decidable` to normalize the instance; restate the
filters `classical`-uniformly; or `conv` into the goal's filter (concrete predicate).

### R6 status: ~70%
Foundations (5) + Step 1 (block-decomposition) proven. Remaining: Step 2 instance fix,
then Step 3 (mod-2 assembly: `card_filter` + `Finset.sum_nat_mod` + Steps 1&2).

## Session 6 — R6 COMPLETE (filter-instance wall cracked) (2026-06-15)

**`promote_anticommute_parity` (R6) is fully proven.** The M3 crux is done; build green.

### The fix
The Step-2 blocker (the goal's `DecidablePred` instance on `Finset.filter (anticommutesAt …)`
wouldn't unify with any `card = 0` term) is **sidestepped by never touching the filter in
the per-block fact**. `cnt_odd_iff` now:
1. converts `Odd (filter …).card` → `Anticommute (ofOperator (promoteSingle … P)) (ofOperator
   (promoteSingle … Q))` via `anticommutes_iff_odd_anticommutes` (passing explicit `ofOperator`
   args so Lean infers the witness instead of failing HO-unification on `.operators`);
2. does the `{I,X,Z}²` case analysis purely with group-level `Anticommute` facts — no filters,
   no instances.

New group lemmas: `one_ne_minusOne`, `not_anticommute_self`, `not_anticommute_one_left/right`
(each forces `1 = -1` via `mul_right_cancel` + phase powers), `ofOperator_identity`.

### R6 chain proven (12 lemmas)
`ofOperator_Xbar/Zbar`, `Xbar_Zbar_anticommute`, `not_anticommutesAt_self`,
`anticommutesAt_promoteE`, `promote_count_eq_sum` (block-decomp, Step 1),
`one_ne_minusOne`, `not_anticommute_self`, `not_anticommute_one_left/right`,
`ofOperator_identity`, `cnt_odd_iff` (Step 2), `promote_anticommute_parity` (Step 3 assembly:
`promote_count_eq_sum` + `Finset.card_filter` + `Finset.sum_nat_mod` + `cnt_odd_iff`).

### Remaining M3 obligations (7, all unblocked by R6)
`concat_generators_commute` (4-case: M1 embedBlock lemmas + inner-logical centralizer + R6),
`concat_closure_no_neg_identity` (Z∪X regroup + CSS lemma), `concat_generators_independent`
(symplectic bridge or `ConcatCSSData` field), and the 4 logical lemmas (R6 + outer logicals).

## Session 7 — concat_generators_commute proven (M3 obligation 1/7) (2026-06-15)

**`concat_generators_commute` proven** (build green) — the linchpin obligation,
the main R6 consumer. 4-case dispatch:
- inner/inner: `embedBlock_commute_iff` / `embedBlock_cross_commute` + `Cin.generators_commute`
- inner/promoted: new `embedBlock_promoteE_commute` (they agree where the inner op is
  non-I, reducing to the inner gen commuting with X̄/Z̄ via centralizer membership)
- promoted/promoted: `commutes_iff_even` + `promote_anticommute_parity` (R6) + `Cout.generators_commute`

New helpers: `inner_gen_comm_logicalX/Z` (centralizer extraction via `mem_centralizer_iff` +
`Subgroup.subset_closure`), `inner_gen_comm_promoteSingle`, `embedBlock_promoteE_commute`,
`outer_gen_noY`, `mem_concatGeneratorsList`.

### Remaining M3 (6 obligations) — scoped
1. **`concat_closure_no_neg_identity`** (fiddly, ~70 lines): regroup `listToSet
   concatGeneratorsList = ZGens ∪ XGens` (set-ext over `inner_split`/`outer_split`
   perms + new `embedBlock_isZ/isX` typing + `promoteE_isZ/isX`), then
   `negIdentity_not_mem_closure_union`. `hZX` is free from `concat_generators_commute`.
2. **`concat_generators_independent`** (hard): block check-matrix independence via the
   `SymplecticSpan` bridge, OR add `rowsLinearIndependent_concat` as a `ConcatCSSData`
   field (structural change to M2) discharged per-instance (`native_decide` at small n).
3-6. **The 4 logical lemmas** — BLOCKED on a structural gap: they need the *outer*
   logicals `(Cout.logicalOps ℓ).xOp/.zOp` to be **Y-free**, which `ConcatCSSData`
   does NOT carry. Fix: augment `ConcatCSSData` (M2) with `outerLogX_isX`/`outerLogZ_isZ`
   (or pointwise no-Y) fields. Then: `_mem_centralizer` via `embedBlock_promoteE_commute`
   (inner gens) + R6 (promoted gens, using outer-logical ∈ Cout centralizer);
   `_anticommute` via an odd-parity analog of R6 (derivable: `Even ↔ Even` ⇒ `Odd ↔ Odd`)
   from `(Cout.logicalOps ℓ).anticommute`; `_commute_cross` via R6 + `Cout.logical_commute_cross`.

Two of the three remaining work-classes (independence field, outer-logical typing)
touch the committed `ConcatCSSData` structure — a deliberate, scoped M2 revision.

## Session 8 — M3 COMPLETE: `concatenate` is sorry-free (2026-06-16)

Closed all 6 remaining M3 obligations. The `concatenate` constructor builds with
zero sorries.

**Scoped M2 revision (safe — no `ConcatCSSData` instances exist yet):** added fields
`outerLogX_isX : ∀ ℓ, IsXType (Cout.logicalOps ℓ).xOp.operators` and
`outerLogZ_isZ : ∀ ℓ, IsZType (Cout.logicalOps ℓ).zOp.operators` to `ConcatCSSData`.
Added reusable helpers in Promotion.lean: `noY_of_isXType`/`noY_of_isZType` (X/Z-type ⇒
no Y component) and `embedBlock_isZ`/`embedBlock_isX` (embedding preserves CSS type);
refactored `outer_gen_noY` onto the noY helpers.

**`concat_closure_no_neg_identity`** — regroup `listToSet concatGeneratorsList = Z ∪ X`
as set-builders (embedded inner Z/X via `inner_split.mem_iff`, promoted outer Z/X via
`outer_split`), typed by `embedBlock_isZ/isX` + `promoteE_isZ/isX`; cross-commutation
free from `concat_generators_commute`; close via
`CSSCommutationLemmas.negIdentity_not_mem_closure_union`. The set-ext reduces, after
`simp` distributes ∃/∨ (`or_and_right`, `exists_or`), to `rw [or_or_or_comm]` (the two
sides differ only by swapping the middle two disjuncts — `tauto` could NOT crunch the
existential atoms, `or_or_or_comm` is exact).

**The 4 logical lemmas:**
- `concatLogicalX/Z_mem_centralizer` — `mem_centralizer_of_commutes_list` (h_closure = `rfl`,
  since `mkStabilizerFromGenerators.toSubgroup` IS the closure) + per-generator dispatch:
  `embedBlock_promoteE_commute` for embedded inner gens, `promote_anticommute_parity` +
  `(Cout.logicalOps ℓ).x/z_mem_centralizer` for promoted outer gens.
- `concatLogical_anticommute` — odd-parity transfer: `anticommutes_iff_odd_anticommutes`,
  then `Odd ↔ ¬Even` (`Nat.not_even_iff_odd`) bridges R6's `Even ↔ Even` to the outer
  pair's `(Cout.logicalOps ℓ).anticommute`.
- `concat_logical_commute_cross` — a local `key` helper (R6 + outer commutation) applied
  to the 4 conjuncts of `Cout.logical_commute_cross ℓ ℓ' hne`.

**`concat_generators_independent` — made an explicit hypothesis of `concatenate`, not derived.**
`StabilizerCode.generators_independent` needs `GeneratorsIndependent` (subgroup independence);
its only proof route is `rowsLinearIndependent` (check-matrix row independence over `ZMod 2`),
which is strictly stronger and NOT recoverable from the subgroup-independence `Cin`/`Cout`
carry (reverse implication false — IndependentEquiv.lean:33). An abstract derivation would
have to add `rowsLinearIndependent` (+ inner-logical symplectic-independence) hypotheses to
`ConcatCSSData` anyway — not cleanly more general, ~200 lines of block linear algebra for no
real gain. Made it a `native_decide`-able side condition (as Steane7/Shor9 do `by decide`):

```
concatenate (D : ConcatCSSData n₁ n₂ k₂)
  (hindep : GeneratorsIndependent (n₁*n₂) D.concatGeneratorsList)
  : StabilizerCode (n₁*n₂) k₂
```

Deleted the sorried `concat_generators_independent` lemma.

### Commits this session
- M3 5/6: 4 logical lemmas + no-neg-I + M2 outer-logical-typing revision
- M3 6/6: `concatenate` sorry-free (independence as explicit hypothesis)

### Next: M4 — `centralizer_classify_of_k1`
The long-pole framework theorem (inner centralizer = stabilizer join `closure {X̄₁, Z̄₁}`).
Per `gap_audit`, the symplectic span↔subgroup bridge it needs already exists
(`SymplecticSpan.lean`), so M4 is reuse, not author-from-scratch. Then M5 (restriction),
M6 (distance ≥ d₁·d₂), M7 (Steane⊗Steane instance — also discharges the `concatenate`
independence hypothesis via `native_decide`).

<!-- Stage-4 runner: append "Session N" sections here as work proceeds. -->







</content>

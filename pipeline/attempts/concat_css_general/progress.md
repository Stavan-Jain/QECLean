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

## Session 9 — M4 started: weak dichotomy proven, decisive kernel scoped + de-risked (2026-06-16)

New module `Framework/Symplectic/CentralizerStructure.lean` (in the
`Framework.Symplectic` umbrella; whole-repo `lake build` clean — global-content
discipline satisfied).

**`centralizer_classify_of_k1` — PROVEN.** The weak inner-centralizer dichotomy: any
`g ∈ centralizer C.toStabilizerGroup` either has its operator part realized by a
stabilizer element (`∃ s ∈ stab, s.operators = g.operators`) or is a nontrivial logical.
Proof = the symplectic-span split (`mem_closure_implies_symp_in_span` /
`exists_mem_closure_of_symp_in_span`) + the three `IsNontrivialLogicalOperator_iff`
clauses. No dimension count, no `k = 1`. **This is the lemma the distance argument's
per-block step actually invokes** (per `informal_spec.md`).

Statement correction vs. the plan: the plan's "trivial branch = `g ∈ stabilizer`"
over-claims (phase subtlety — `g` may be a phased copy of a stabilizer element, hence
neither in the stabilizer nor a *nontrivial* logical). The phase-clean operator-part form
is what is true and what downstream consumes; it subsumes the plan's separate
`mem_stabilizer_of_operators_eq`.

**`operators_eq_stab_of_commutes_both_logicals` — SCOPED `sorry` (the long pole).**
Reduced to the clean symplectic core goal `toSymplectic g.operators ∈ sympSpan
C.generatorsList`. The remaining mathematical content is the `k = 1` dimension-2 quotient
fact `sympOrthogonal(span{stab rows, X̄, Z̄}) = span(stab rows)`.

**Feasibility (de-risked this session):** mathlib **provides the hard dimension lemma** —
`LinearMap.BilinForm.finrank_orthogonal (hB : B.Nondegenerate) (W) : finrank (B.orthogonal
W) = finrank V - finrank W` (`Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean:280`),
valid over any field (`ZMod 2` qualifies; `V = Fin (n+n) → ZMod 2` is finite-dim). So the
kernel is **feasible, not blocked**. Remaining build (~150–250 LOC):
1. Bundle `symplecticBilinear` as a `LinearMap.BilinForm (ZMod 2) (Fin (n+n) → ZMod 2)`
   and prove `Nondegenerate` (the form's matrix `J = [[0,I],[I,0]]` satisfies `J² = I`).
2. Identify `B.orthogonal W` with the repo's `sympOrthogonal W`.
3. `finrank (sympSpan L) = n − 1` from row-independence (`finrank_span_eq_card` on the
   independent `checkMatrix` family).
4. `finrank (span{rows, X̄, Z̄}) = n + 1` (rows independent; `X̄, Z̄ ∉ span rows` via
   `not_mem_subgroup_of_symp_not_in_span`; `X̄, Z̄` independent of each other via their
   anticommutation = symplectic non-orthogonality).
5. Containment `span rows ⊆ sympOrthogonal(span{rows, X̄, Z̄})` + equal dim ⇒ equality;
   then `symp(g) ∈ that orthogonal = span rows`.

**Design decision the kernel forces:** it needs **row-independence of the inner
generators** (`rowsLinearIndependent Cin.generatorsList`), which `StabilizerCode` does NOT
carry (only the weaker subgroup `GeneratorsIndependent`; the reverse implication is false).
Resolution mirrors the M3 independence call: add `rowsLinearIndependent`-flavored fields to
`ConcatCSSData` (or hypotheses to the kernel lemma), discharged per-instance by
`native_decide` (Steane: `by decide`, as Steane7 already does). Plus the inner-logical
symplectic-independence facts (derivable from `X̄/Z̄ ∈ centralizer \ stabilizer` and their
anticommutation).

### Commit this session
- M4 weak dichotomy proven; decisive kernel reduced to the symplectic in-span goal and
  scoped (CentralizerStructure.lean).

### Next: the M4 dimension kernel (per items 1–5 above), then M5/M6/M7.
M5/M6 must not start before the kernel closes (unsound otherwise — gap_audit).

## Session 10 — M4 COMPLETE: the decisive dimension kernel proven (2026-06-16)

`CentralizerStructure.lean` is now fully `sorry`-free. The long pole
`operators_eq_stab_of_commutes_both_logicals` is proven.

**Phase 1 — nondegenerate symplectic `BilinForm`.** Bundled `symplecticBilinear` as a
mathlib `LinearMap.BilinForm (ZMod 2) (Fin (n+n) → ZMod 2)` (`sympBilinForm`); proved
symmetric (`symplecticBilinear_comm`), reflexive, and `Nondegenerate` (separating-left via
`Pi.single` basis-vector extraction over the two `Fin (n+n)` halves).

**Phase 2 — the dimension count.** Two reusable helpers:
`mem_sympBilinForm_orthogonal_span_iff` (orthogonal membership ↔ orthogonality vs the
spanning set) and `sympBilinForm_orthogonal_sup` (orthogonal sends `⊔` to `⊓`). Then the
k=1 dimension-2 argument with `V = sympSpan L`, `U = span{X̄,Z̄}`, `W = V ⊔ U`:
`symp(g) ∈ Wᗮ`; `dim V = n−1` (`finrank_span_eq_card` on the independent rows);
`dim U = 2` (the anticommuting pair independent via `LinearIndependent.pair_iff` + the
symplectic pairing values); `V ⊓ U = ⊥` (logicals ⊥ V); so `dim W = n+1`
(`finrank_sup_add_finrank_inf_eq`) and `dim Wᗮ = 2n−(n+1) = n−1` (mathlib
`BilinForm.finrank_orthogonal`, nondegenerate); `V ⊆ Wᗮ` + equal dim ⇒ `V = Wᗮ`
(`eq_of_le_of_finrank_eq`), whence `symp(g) ∈ V`.

**Gotchas this session (for future BilinForm work in this repo):**
- The `orthogonal` / `finrank_orthogonal` API lives in
  `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`, which was NOT transitively imported
  (Phase 1 only pulled BilinForm *Basic*). Symptom: `Unknown constant
  LinearMap.BilinForm.orthogonal` and a cascading `motive`/`m ∈ sorry`. Fix: add the import.
- `BilinForm` is `open LinearMap (BilinForm)` over a reducible arrow type, so `(B).orthogonal`
  dot-notation resolves to the nonexistent `LinearMap.orthogonal`. Use fully-qualified
  `LinearMap.BilinForm.orthogonal B N`. Do NOT `open LinearMap.BilinForm` — it breaks the
  fully-qualified resolution.
- `finrank (ZMod 2) (P ⊔ Q)` elaborates the `⊔` with expected type `Type` → `failed to
  synthesize Max Type`. Write `finrank (ZMod 2) ↥(P ⊔ Q)`.
- `mul_one` is ambiguous (`_root_.mul_one` vs `NQubitPauliGroupElement.mul_one`); qualify
  `_root_.mul_one` in `simp` sets. `mul_zero` is fine unqualified.
- Don't `rw` a `Nat` (e.g. `generatorsList.length`) that also indexes a `Fin` — the motive
  fails; rewrite a standalone copy instead.

### Commits this session
- M4 kernel phase 1 (nondegenerate BilinForm).
- M4 COMPLETE (decisive dimension kernel).

### Next: M5 (block restriction + induced-outer correspondence), then M6 (distance), M7.
M4 unblocks them: `centralizer_classify_of_k1` for the per-block split,
`operators_eq_stab_of_commutes_both_logicals` for the induced-outer coset injectivity.
M7's Steane⊗Steane instance discharges both the `concatenate` independence hypothesis and
the inner `rowsLinearIndependent` (M4) hypothesis by `native_decide`.

<!-- Stage-4 runner: append "Session N" sections here as work proceeds. -->

## Session 11 — M5 (block restriction + induced-outer correspondence)

Three commits, three phases. M5 infrastructure fully proven; one scoped symplectic
kernel remains.

### Phase 1 — `Framework/Concatenation/Restriction.lean` (sorry-free)
- `restrictBlock b g` = read off block `b` of an `n₁·n₂`-qubit operator as a phase-0
  inner Pauli (`ofOperator (fun i => g.operators (qIdx b i))`).
- `weight_eq_sum_restrictBlock`: `g.weight = ∑ b, (restrictBlock b g).weight` — via
  `weight_eq_sum_block_weights` (M1) + `image_qIdx_support_restrictBlock` (qIdx-image of
  the restriction support = the block-`b` fiber of `g.support`).
- `anticommutesAt_count_restrictBlock`: count parity bridge dual to `anticommutesAt_count_eq`,
  via a per-position helper `anticommutesAt_restrictBlock_iff` (mirrors
  `anticommutesAt_embedBlock_iff`).
- `restrictBlock_commute_embed_iff` and `restrictBlock_mem_centralizer`: `g ∈ centralizer
  concat ⟹ restrictBlock b g ∈ centralizer Cin` (each `embedBlock b s` is a concat
  generator). The hinge for applying M4 per block.

### Phase 2 — `Framework/Concatenation/Correspondence.lean` (sorry-free)
- `inducedOuterOp` / `inducedOuter`: per-block inner-logical class from commutation with
  `X̄₁/Z̄₁` (nested `if Anticommute …`, `open Classical`).
- `inducedOuterOp_eq_I_iff` + per-block bridge `induced_block_anticommute_iff` (single-block
  analogue of `cnt_odd_iff`; `rcases h.operators b` then `split_ifs with h1 h2 h3` +
  `iff_of_true/false (by decide) (by assumption)`).
- `count_promoteE_eq_sum_restrict` + `induced_count_mod_two` + `induced_commute_iff`: the
  induced parity bridge (dual of `promote_anticommute_parity`); for Y-free `h`,
  `inducedOuter` commutes with `h` ↔ `g` commutes with `promoteE h`.
- `inducedOuter_mem_centralizer` (promoted outer gens are concat gens).
- `restrict_commutes_both_iff_stab` (uses M4 `operators_eq_stab_of_commutes_both_logicals`
  forward; operator-part commutation backward) → `inducedOuter_support_eq`:
  `b ∈ support(inducedOuter) ↔ restrictBlock b g is a nontrivial inner logical`.

### Phase 3 — coset injectivity reduced to one scoped kernel (Correspondence.lean)
- `inducedOuter_symp_in_span` (the ONLY `sorry`, R7): an outer stabilizer matching
  `inducedOuter`'s operator part ⟹ `toSymplectic g ∈ sympSpan(concatGeneratorsList)`.
  Full proof plan in its doc-comment (disjoint-support gluing + symplectic embed/promote
  maps into `sympSpan concat` + per-block M4 kernel).
- PROVEN unconditionally from it: `inducedOuter_coset_injective` (via
  `exists_mem_closure_of_symp_in_span`), `inducedOuter_not_mem_stabilizer`,
  `inducedOuter_isNontrivialLogical` (the M5 headline). Mirrors how M4 isolated its kernel.

### Gotchas this session
- `(restrictBlock b g).operators` shows as `restrictBlockOp b g` after some rewrites but not
  others (defeq via `ofOperator_operators`); match the form the goal actually displays
  (`rw [← hsop]` vs `rw [show restrictBlockOp … = …]`).
- `rcases hPb : h.operators b` substitutes the scrutinee where it appears as a direct
  subterm (RHS `promoteSingle … (h.operators b)`) but NOT inside `anticommutesAt … h.operators b`
  (there it's the partial app `h.operators`); rely on a later `simp only [… hPb]` to finish.
- Nested `if c1 then (if c2 …) else (if c2 …)` needs `split_ifs with h1 h2 h3` (three names:
  the second `c2` split gets `h3`); `by assumption` then finds whichever `c2`-hyp is in scope.
- `≠` (= `Ne`) hides the inner `= I` from `rw`; insert `ne_eq` first.
- `Finset.sum_nat_mod` rewrites the first `(∑) % 2`; use `conv_rhs => rw [Finset.sum_nat_mod]`
  to target the intended side.

### Commits this session
- M5 phase 1 (block-restriction calculus).
- M5 phase 2 (induced outer logical: support_eq + centralizer).
- M5 phase 3 (nontriviality reduced to one scoped symplectic kernel).

### R7 kernel (this session, continued): `inducedOuter_symp_in_span` now PROVEN.
Two more commits drove the R7 kernel from "one big sorry" to "proven, modulo one deeper
existence lemma":

- `Restriction.lean`: `toSymplectic_eq_sum_embed_restrictBlock` (symplectic gluing — per
  coordinate only the `blockOf q` summand survives) and `toSymplectic_embedBlock_mem_concatSpan`
  (embed preserves the span; `exists_mem_closure_of_symp_in_span` + `closure_induction`, using
  `mulOp_embedBlockOp_operators` for additivity and `inv_operators` for the inverse case). Both
  sorry-free.
- `Correspondence.lean`: `inducedOuter_symp_in_span` fully assembled and PROVEN —
  `toSymplectic g = toSymplectic (g*u) + toSymplectic u` over `ZMod 2`
  (`CharTwo.add_self_eq_zero`), with `toSymplectic (g*u) ∈ sympSpan` from gluing + embed-span +
  the M4 kernel (each `restrict b (g*u)` is inner-stabilizer-like) and `toSymplectic u ∈ sympSpan`
  from `u ∈ concat.stab`.

**Key correctness insight discovered:** `promoteE t` is LOSSY on `Y` (`promoteSingle Y = I`),
so the naive "promote `t`" correction fails on Y-class blocks. The matching stabilizer `u` must
be the concat-GROUP product of promoted Y-free generators — the group multiplication realizes
the `Y = X̄₁Z̄₁` class on Y-blocks correctly. This is recorded in the scoped lemma's doc-comment.

The single remaining concat sorry: `exists_concatStab_matching_induced` (the class-matching `u`
via `closure_induction` on `t`, with the `inducedOuterOp` class-homomorphism). Plan in
`state.yaml`'s `next_step`.

### Gotchas (R7 continued)
- The MCP LSP serves a STALE import olean for a sibling file edited earlier the same session:
  after adding lemmas to `Restriction.lean`, `lean_diagnostic_messages` on `Correspondence.lean`
  reported the new names as "unknown identifier" even though `lake build` resolved them fine.
  Confirm cross-file references with `lake build`, not the LSP, after editing a dependency.
- `≠` is `Ne` (hides the `= I`); `Finset.sum_nat_mod` hits the first `(∑)%2`; `Fin.addCases`
  to split a symplectic index into X-part/Z-part (`toSymplectic_X_part`/`_Z_part`).

### R7 CLOSED — M5 fully proven, sorry-free.
`exists_concatStab_matching_induced` is now proven, so the whole concatenation development is
sorry-free (whole-repo `lake build` green, 3433 jobs).

Proof of `exists_concatStab_matching_induced` (the class-matching concat stabilizer `u`):
- Work with the ZMod 2 *signature* `(symplecticInner (restrict b ·) Z̄₁, symplecticInner (restrict
  b ·) X̄₁)` rather than the Pauli class — it is genuinely bilinear, dodging the Y-handling
  trap entirely.
- `symplecticInner_group_mul_left` / `symplecticInner_restrictBlock_mul`: bilinearity of
  `symplecticInner` under the group product, via the M4 `symplecticBilinear` + `toSymplectic_mul`
  (the restriction of a product multiplies block-wise, so its inner product is additive).
- `inducedOuterOp_toSymplecticSingle`: the induced class Pauli's `(x,z)` bits ARE the signature
  (`split_ifs <;> rfl` after rewriting each `symplecticInner` to its `if Anticommute … then 1
  else 0` form).
- `Subgroup.closure_induction` on `t ∈ Cout.stab` builds `u ∈ concat.stab` with `signature(u) =
  toSymplecticSingle ∘ t.operators`: the `mem` case promotes a Y-free outer generator (signature
  = the generator's own `toSymplecticSingle`, computed from `X̄₁ Z̄₁` (anti)commutation); the
  `mul` case uses `toSymplecticSingle_add`; `one`/`inv` are immediate. **The concat-group product
  is what makes the `mul` case work for Y — `promoteE t` alone is lossy.**
- Conclusion: `signature(u) = signature(g)` (via `htop` + `inducedOuterOp_toSymplecticSingle`), so
  `symplecticInner (restrict b (g*u)) L = signature_L(g) + signature_L(u) = 0` (`CharTwo`) — i.e.
  `restrict b (g*u)` commutes with both inner logicals.

### Gotchas (R7 final)
- The `if Anticommute …` needs `classical` in scope (the `Decidable (Anticommute …)` instance is
  noncomputable); matches `inducedOuterOp`'s own `open Classical`.
- Lemmas using `symplecticInner` / `commutes_iff_symplectic_inner_zero` etc. need
  `open NQubitPauliOperator in` (they live in that namespace).
- `omit [NeZero n₁] in` on the general `symplecticInner_restrictBlock_mul` (it doesn't use it).

## Session 12 — M6 (distance) DONE, sorry-free.

`Framework/Concatenation/Distance.lean`:
- `weight_ge_d1_mul_d2`: every nontrivial concat logical has weight ≥ d₁·d₂. Assembled exactly
  as planned — `inducedOuter_support_eq` makes the nontrivial-block set the support of
  `inducedOuter`, `inducedOuter_isNontrivialLogical` + `HasCodeDistance.min_weight Cout` gives
  ≥ d₂ such blocks, `HasCodeDistance.min_weight Cin` gives ≥ d₁ each, `weight_ge_of_blocks_ge`
  (M1) sums it. Helpers: `weight_pos_of_nontrivial` (nontrivial ⟹ weight>0 via
  `weight_eq_zero_iff` + the identity stabilizer), `card_block_filter_eq_restrictBlock_weight`.
- `concat_hasCodeDistance : HasCodeDistance (concatenate D) (d₁·d₂)`. Lower bound from the
  above; `d₁·d₂ ≥ 1` from `Nat.mul_pos`. The exact-distance WITNESS is an explicit hypothesis:
  the weight-(d₁·d₂) nontrivial logical depends on the codes' minimum-weight representatives,
  which abstract `ConcatCSSData` does not pin down (the fixed `concatLogicalX D ℓ` has weight
  ≥ d₁·d₂ but not necessarily =). It is discharged concretely in M7.

Gotchas: `HasCodeDistance.min_weight`/`one_le_d` have `C d` as explicit args *before* the
`HasCodeDistance` arg, so dot notation misbinds — use full application
`HasCodeDistance.min_weight D.Cin d₁ h1 _ hnt hpos`. The bridge
`(concatenate D hindep).toStabilizerGroup = concatStabGroup D` holds by `rfl` (defeq), so the
M5 lemmas (stated against `concatStabGroup D`) apply directly to `concat_hasCodeDistance`'s
`(concatenate D).toStabilizerGroup` hypotheses with no explicit conversion.

### Next: M7 (Steane⊗Steane [[49,1,9]], the validating instance).
`steaneConcatData : ConcatCSSData 7 7 1` from `Steane7.stabilizerCode` (Cin=Cout); the
structural fields are easy (`generatorsList = [Z1,Z2,Z3,X1,X2,X3] = innerZ++innerX`, so
`inner_split = Perm.refl`; types from `ZGenerators_are_ZType`/`XGenerators_are_XType`; logicals
all-X/all-Z phase-0). **Friction:** `native_decide` for the 48-generator/49-qubit
`GeneratorsIndependent` and the d=9 witness needs a COMPUTABLE restatement of
`concatGeneratorsList` (it flows through `Steane7.stabilizerCode`'s noncomputable fields;
`native_decide` needs compiled code). Plan: `concatGeneratorsList steaneConcatData = <explicit
computable list from Steane7.generatorsList + logical ops>` by `rfl`/`decide`, then
`native_decide`.

## Session 13 — M7 (partial): bundle + Steane d=3 + conditional [[49,1,9]].

`steaneConcatData : ConcatCSSData 7 7 1` typechecks (the framework's input bundle instantiates
on Steane). The 16 fields are easy: `inner_split/outer_split = Perm.refl` (`generatorsList =
[Z1,Z2,Z3]++[X1,X2,X3]`); Z/X-type from `ZGenerators_are_ZType`/`XGenerators_are_XType` (list→set
membership by `simp`); logical type/phase by `fun _ => Or.inr rfl` / `rfl` (the all-X/all-Z
operators reduce to `X 7`/`Z 7`; `by decide` fails — noncomputable term + free `ℓ`).

**Steane distance-3 PROVEN** (`Steane7Distance.lean`, sorry-free) —
`stabilizerCode_hasCodeDistance_three`, the inner/outer distance M6 consumes:
- weight-3 witness `logicalX_w3 = X on {3,5,6}` (explicit `ofOperator`, `= logicalX·X1`); the
  3-part nontriviality copies the FiveQubit pattern (`anticommute_of_operators_eq` lifted local).
- weight-1: `weight_one_anticomm_witness` by `fin_cases i <;> match P <;> first | ⟨gen, by simp, by decide⟩`.
- weight-2: the 7·7·4·4 table **times out** via `Anticommute`-`decide` (200000 heartbeats — the
  noncomputable `*` makes each `decide` a heavy kernel `whnf`). FIX: recast through the
  *computable* `symplecticInner = 1` and close by **`native_decide`** (~ms), then convert with
  `anticommutes_iff_symplectic_inner_one`. File-local `DecidableEq`/`decidableAnticommute`
  instances (mirroring FiveQubit) — NOT global (the global ones break RotatedSurface's
  native_decide; see Commutation.lean's removed-instance note).

**Conditional [[49,1,9]]** — `steaneConcat_hasCodeDistance_nine` instantiates M6's
`concat_hasCodeDistance` with Steane d=3 for both inner & outer, leaving exactly two hypotheses:
the concat `GeneratorsIndependent` and a weight-9 witness.

### KEY FINDING: the concat independence is not `native_decide`-able.
`Decidable (rowsLinearIndependent L)` (`CheckMatrixDecidable.lean`) enumerates all `2^L.length`
coefficient vectors. For the concat code that's `2^48` → OOM (exit 137). The plan's R5
"native_decide per instance" fallback works only for small single codes (Steane: `2^6`). The
real fix is a **structural** `rowsLinearIndependent_concat` lemma (disjoint block-supports of
embedded inner gens + inner logicals ∉ inner rowspan) — ≈M4-scale, deferred.

### Next: unconditional [[49,1,9]] needs (A) structural concat-independence lemma, (B) a
computable weight-9 witness. Both are new framework work; everything else is in place.

---

## Session 14 — (A) the structural concat-independence lemma: DONE

New module `Framework/Concatenation/Independence.lean` (~410 LOC, sorry-free; axioms of the
headline = `{propext, Classical.choice, Quot.sound}` only — **no `native_decide` trust**).

**Headline:** `ConcatCSSData.rowsLinearIndependent_concat` (and its `GeneratorsIndependent`
corollary `generatorsIndependent_concat`) derives the `2^48`-infeasible concat-generator
independence from **two small inputs**:
- `hin : rowsLinearIndependent (Cin.generatorsList ++ [X̄₁, Z̄₁])`  (Steane: `2^8`)
- `hout : rowsLinearIndependent (outerZ ++ outerX)`                  (Steane: `2^6`)

**Engine — `blockRestrictSymp b` LinearMap.** Built as `LinearMap.funLeft` of a coordinate map
`blockEmbedIdx b` (so linearity is free), it reads off block `b`'s symplectic coordinates;
`blockRestrictSymp_toSymplectic` shows it commutes with `toSymplectic ∘ operators` and
`restrictBlock b`. Two facts power everything: an embedded inner gen restricts to the gen on its
own block and to `0` elsewhere; a promoted outer gen restricts to a combination of `X̄₁, Z̄₁`
(via `outer_gen_noY`, since `promoteSingle` is lossy on `Y`).

**Proof skeleton:**
1. `rowsLinearIndependent_append_iff` (general, in `NQubitPauliGroupElement`): reindex the row
   family along `Fin A.length ⊕ Fin B.length ≃ Fin (A++B).length` (`finSumFinEquiv`/`finCongr`)
   and apply mathlib's `linearIndependent_sum`. Splits a list-append into independence of each
   half + disjoint `sympSpan`s. Used both to *destructure* `hin` and to *assemble* the concat.
2. Inner part (`s1PerBlockList`, a `flatMap` over blocks): induction on a `Nodup` block list,
   each step `append_iff` with the per-block map (`rowsLinearIndependent_map_embedBlock`, via
   `blockRestrictSymp` being a left inverse on its block) + disjointness from
   `blockRestrictSymp` vanishing on every other block.
3. Promoted part: each `blockRestrictSymp b` of `∑ βₜ·pr(t)` is `c₁·X̄₁ + c₂·Z̄₁`; `hin`'s
   logical-independence kills both coefficients at every block, which reassembles into an outer
   relation killed by `hout`.
4. Disjointness of the inner and promoted spans: every block restriction of a shared vector lies
   in `sympSpan(Cin.gens) ⊓ span{X̄₁, Z̄₁} = 0` (from `hin`), so the vector is `0`
   (`eq_zero_of_forall_blockRestrictSymp_zero`).

**Steane discharge** (`SteaneSteane.lean`): `steaneConcat_generatorsIndependent` proves
`GeneratorsIndependent 49 …` by `native_decide` on the two small concrete inputs (the
`stabilizerCode` projections reduce to `generatorsList`/`logicalX`/`logicalZ` by `rfl`).
`steaneConcat_hasCodeDistance_nine` now **drops the `hindep` hypothesis** — only the weight-9
witness `hwit` remains.

mathlib-API notes (v4.30): `linearIndependent_sum`, `linearIndependent_equiv`,
`LinearIndependent.of_comp`, `Fintype.linearIndependent_iff`, `LinearMap.funLeft[_apply]`,
`finSumFinEquiv_apply_left/right`, `finCongr`, `List.getElem_append_left/right`,
`List.getElem_map`, `List.flatMap_cons`, `List.mem_flatMap`, `List.nodup_finRange`,
`Submodule.{map_span,span_le,disjoint_def}`. Quirks: `List.length_append`/`List.mem_cons_self`
take implicit args (use `by rw`/`by simp`); the `show` that changes a goal is a linter error
(use `change`); `IsEmpty (Fin [].length)` needs a `haveI` (no auto-reduce of `[].length`).

## Session 14 (cont.) — (B) the weight-9 witness: DONE → **unconditional [[49,1,9]]**

`steaneConcat_hasCodeDistance_nine : HasCodeDistance (steaneConcatData.concatenate …) 9` now
takes **no hypotheses**. `#print axioms` = `{propext, Classical.choice, Quot.sound}` + the
`native_decide` axioms only — **no `sorryAx`**.

**Witness** (`SteaneSteane.lean`, `steaneConcat_witness`): `witnessE = X` on the inner `{3,5,6}`
of the three active outer blocks `{3,5,6}` (9 qubits) — the inner weight-3 logical promoted onto
the outer weight-3 logical's support. Nontriviality via the centralizer-anticommutes pattern:
- `witnessE_weight : weight = 3·3` by `native_decide`.
- `witnessE_mem_centralizer` / `allZ_mem_centralizer`: `mem_centralizer_of_commutes_list` with
  `∀ s ∈ concatGensConcrete, symplecticInner s.op _ = 0` by `native_decide`.
- `allZ = ⟨0, Z 49⟩` is a centralizer member anticommuting with `witnessE`
  (`symplecticInner witnessOp (Z 49) = 1`), so `not_mem_stabilizer_of_anticommutes_centralizer`
  gives both `∉ subgroup` and (with a local `anticommute_of_operators_eq`) the third
  `IsNontrivialLogicalOperator` clause.

**The key trick — concrete-list bridge for `native_decide`.** `steaneConcatData.concatGeneratorsList`
is *not* native-computable (its `stabilizerCode` projections sit behind a `noncomputable def`),
so `native_decide` on it fails. Fix: define `concatGensConcrete` — the same list with the
projections written as the explicit `generatorsList` / `logicalX` / `logicalZ` — which **is**
`rfl`-equal to it (the projections reduce by `rfl`). Run every `native_decide` against
`concatGensConcrete`; pass it to `mem_centralizer_of_commutes_list` with `h_closure := rfl`
(`concatStabGroup.toSubgroup ≡ closure (listToSet concatGensConcrete)`). This is the same
defeq-bridge used for `steaneConcat_generatorsIndependent`, and is the general recipe for
`native_decide` against any value behind a noncomputable concrete-data projection.

### M7 COMPLETE. Entire M1–M7 concatenation program done and sorry-free.
Optional next: open a PR; promote reusable patterns (blockRestrictSymp, append-independence,
the noncomputable→concrete+rfl+native_decide bridge) to `lean-patterns.md`; generalize beyond
`k1 = 1` or instantiate other inner⊗outer pairs.


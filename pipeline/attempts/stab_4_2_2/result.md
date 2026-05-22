# Result: stab_4_2_2

## Status
`pr-ready`

## Sorries closed
22/22. By theorem name (in plan order):

| # | Theorem | Closing tactic / approach |
|---|---|---|
| T1 | `ZGenerators_are_ZType` | `rcases ... with rfl; refine ⟨rfl, ?_⟩; intro i; fin_cases i <;> simp [PauliOperator.IsZType, Z1, NQubitPauliOperator.set]` |
| T2 | `XGenerators_are_XType` | analogous to T1, with `IsXType`/`X1`. |
| T3a | `Z1_comm_X1` | `pauli_comm_even_anticommutes` + `hfilter = {0,1,2,3}` (Steane7:136 pattern). |
| T3 | `ZGenerators_commute_XGenerators` | singleton `rcases` + T3a. |
| T4 | `generators_commute` | union case-split with `ZType_commutes`/`XType_commutes`/T3 (Steane7:260 pattern). |
| T5 | `negIdentity_not_mem` | `CSS.negIdentity_not_mem_closure_union` (Steane7:277 pattern). |
| T6a | `listToSet_generatorsList` | `simp only [generatorsList, generators, …] + ext + simp only` (Steane7:290 pattern). |
| T6b | `rowsLinearIndependent_generatorsList` | `by decide`. |
| T6c | `stabilizerGroup_toSubgroup_eq` | `simp only + rw [listToSet_generatorsList]`. |
| T7 | `AllPhaseZero_generatorsList` | two nested `AllPhaseZero_cons` (Steane7:320 pattern, two cases). |
| T8a | `logicalX_1_anticommutes_logicalZ_1` | `pauli_anticomm_odd_anticommutes` + `hfilter = {3}` (odd, anticommute). |
| T8b | `logicalX_2_anticommutes_logicalZ_2` | same, `hfilter = {3}`. |
| T9a | `logicalX_1_commutes_logicalX_2` | `pauli_comm_componentwise` (both X-type). |
| T9b | `logicalX_1_commutes_logicalZ_2` | `pauli_comm_even_anticommutes` + `hfilter = {1,3}`. |
| T9c | `logicalX_2_commutes_logicalZ_1` | `pauli_comm_even_anticommutes` + `hfilter = {2,3}`. |
| T9d | `logicalZ_1_commutes_logicalZ_2` | `pauli_comm_componentwise` (both Z-type). |
| T10a | `logicalX_1_mem_centralizer` | `Subgroup.forall_comm_closure_iff` + two helpers (vs. Z1: `hfilter={1,3}`; vs. X1: componentwise). |
| T10b | `logicalX_2_mem_centralizer` | analogous, `hfilter={2,3}` vs Z1. |
| T11a | `logicalZ_1_mem_centralizer` | analogous, `hfilter={2,3}` vs X1. |
| T11b | `logicalZ_2_mem_centralizer` | analogous, `hfilter={1,3}` vs X1. |
| T12 | `stabilizerCode.logical_commute_cross` | `fin_cases ℓ <;> fin_cases ℓ'`; (0,0) and (1,1) closed by `(hne rfl).elim`; (0,1) and (1,0) by `refine ⟨T9a, T9b, T9c.symm, T9d⟩` and `.symm` variants. **First true k=2 packaging in the repo — no `Subsingleton.elim` shortcut applies.** |
| T13 | `code_has_distance_two` | `hasCodeDistance_of` with `decide` for `hd` and witness weight; for `h_min`, `interval_cases w` collapses to `w=1`, then `no_weight_one_mem_centralizer_of_anticommute_witness` from `Core/CSSDistance.lean` finishes. |

## Blocked sorries
None.

## Lines of Lean produced
**547 LoC** (post-golf), vs. estimated 300.

Overrun explained by:
- k=2 expansion of T10/T11 (8 centralizer-commutation helpers, vs. Steane7's 6 for k=1; can't share via `Subsingleton.elim`).
- T13's witness-helper lemmas (2 reusable lemmas, ~35 LoC) — the alternative of inlining the 12-case enumeration would have been worse.
- Comments + doc strings + section headers (skeleton already had ~70 LoC of these; non-load-bearing).

## Time spent
- Setup + reading reference patterns: ~10 min.
- T1–T11 (mechanical, Steane7-template): ~20 min total, no subagent escalation.
- T12 (k=2 packaging): ~5 min — `fin_cases <;> fin_cases` worked first try.
- T13 (distance enumeration): ~25 min — needed to discover `no_weight_one_mem_centralizer_of_anticommute_witness` (pre-existing in `Core/CSSDistance.lean`, previously unused) and debug the `decide` free-variable trap.
- Linter cleanup + golf pass: ~10 min.
- **Total: ~70 min wall-clock.** Well under the 8h cap.

Subagent delegations: zero. The full proof was direct adaptation of patterns from `Steane7.lean` and `RepetitionCode3.lean`, plus the discovery of `CSSDistance.lean`'s pre-existing helper.

## Patterns discovered

These are worth adding to CLAUDE.md for future runs:

1. **`Core/CSSDistance.lean` has a pre-existing `no_weight_one_mem_centralizer_of_anticommute_witness`** that handles distance-2 (and any "no weight-1 logical") arguments cleanly. Until this attempt, it was completely unused — the file had no downstream importers. Worth surfacing it in the `gap_audit`/`reuse_audit` checklist for any d=2 code (e.g. the `[[4,2,2]]` and any future d=2 detection codes). The file is now imported and exercised.

2. **k=2 `logical_commute_cross` packaging is straightforward** via `fin_cases ℓ <;> fin_cases ℓ'` over `Fin 2`. The `(hne rfl).elim` closes the diagonal cases (where `ℓ = ℓ'` contradicts the hypothesis), and the off-diagonal cases (0,1) and (1,0) are dispatched by the four off-diagonal commutation lemmas T9a–T9d plus their `.symm`. Total: ~10 lines. No new `Core/` machinery needed — the bookkeeping was simpler than the `gap_audit.md` anticipated.

3. **`decide` trap on `Odd ({i} : Finset (Fin n)).card`**: when the variable `i` is a free Fin-valued variable (post-`fin_cases`/`match` substitution), `rw [hfilter]; decide` fails with "Expected type must not contain free variables". Workaround: `rw [hfilter]; simp +decide`. Already noted in CLAUDE.md's general principle ("`simp +decide` is preferred over hand-written `decide`"); this is a concrete instance worth tagging — the issue specifically arises when the singleton's element is universally quantified rather than concrete.

4. **`cases hP_cases : P with` vs `match P, hP with`**: the `cases` form substitutes `P` in the goal but **not** in `have hfilter` introduced earlier with `P` still appearing. The `match` form is cleaner — the pattern variable carries through to the binders. Used `match` for T13's witness function.

5. **Three-bullet expansion of the `IsNontrivialLogicalOperator` destructure**: the third conjunct (`∀ s ∈ S.toSubgroup, s.operators ≠ g.operators`) is **never used in T13** — only the first conjunct (centralizer membership) is needed once you have an anticommuting stabilizer. Pattern:
   ```lean
   rcases (IsNontrivialLogicalOperator_iff g _).mp h_nontrivial with ⟨h_cent, _, _⟩
   ```
   Use `_` for the two unused conjuncts.

## Suggested follow-ups

1. **Lift `no_weight_one_mem_centralizer_of_anticommute_witness` into the documented reuse path.** It's currently in `Core/CSSDistance.lean` but not referenced anywhere else and not mentioned in the `reuse_audit.md` template (the audit cited `anticommutes_imp_not_isPauliLogicalOperator` and `RepetitionCode3.Z_on_qubit2_operators_ne_of_mem`, both of which are heavier than necessary for d=2). Update the reuse-audit checklist for the d=2 case to surface this helper first.

2. **Consider a `LogicalQubitOps.cross_commute_pair` smart constructor** (suggested in `gap_audit.md` item 1) to package the ∧-of-4-eqs more ergonomically. With one k=2 instance now in the repo, the value is clearer — but for n=4 with only one off-diagonal pair (and its symm), the current `refine ⟨...⟩` pattern is fine. Recheck this after the second or third k=2 code lands (e.g. `[[5,1,3]]` is k=1; if anyone formalizes `[[10,4,3]]` or similar, the bookkeeping will balloon).

3. **`distance_two_from_full_X_full_Z` as a reusable Core lemma** (gap_audit.md item 2). The pattern in T13 — `XXXX` and `ZZZZ` together rule out all weight-1 Paulis — generalizes to any CSS code with at least one all-X and one all-Z generator. The current proof is ~70 LoC at the call site (helpers + dispatch). Worth promoting if a second d=2 code arrives.

4. **CLAUDE.md update**: add the four "patterns discovered" items above to the v4.30 cheatsheet section. The `decide` trap on `({i} : Finset _).card` and the `match P, hP with` vs `cases hP_cases : P` pattern are both general — they'd save the next agent 5–10 minutes of debugging.

5. **HasCodeDistance.detects_errors** translation (gap_audit.md item 3) — out of scope for this Stage 4, but worth a follow-up Stage-2 ticket if anyone wants to claim the code's "detects single-qubit errors" property formally.

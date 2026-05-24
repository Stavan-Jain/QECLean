# Progress log: iceberg `[[2m, 2m−2, 2]]`

## Session 1 (2026-05-24)

- Starting sorries: 24 across T1–T19 (some Ti have multiple helper sub-sorries)
- Skeleton parses cleanly with `lake build QEC.Stabilizer.Codes.Iceberg.N`
- Worktree symlink to main repo's `.lake/packages` confirmed
- Plan order from `plan.md`: T1, T2, T3 (+bundle), T4, T5, T6, T7, T8, T10, T11, T12a, T12b, T12c, T13-helpers (×2), T14-helpers (×2), T13, T14, T15, T16, T17, T18

### Closed so far in this session

- T1 (ZGenerators_are_ZType): direct unfold; per-qubit Or.inr `S_Z` is constant Z
- T2 (XGenerators_are_XType): mirror of T1
- T3 (S_Z_comm_S_X): pauli_comm_even_anticommutes + filter = univ; cardinality = 2m, even via `⟨m, by ring⟩`
- T3-bundle (ZGenerators_commute_XGenerators): rcases on singletons + S_Z_comm_S_X
- T4 (generators_commute): 4-way rcases dispatch via Z/X-type commutes + T3
- T5 (negIdentity_not_mem): CSS.negIdentity_not_mem_closure_union via T1/T2/T3
- T6 (listToSet_generatorsList): direct simp on Set extensionality
- T7 (AllPhaseZero_generatorsList): chain AllPhaseZero_cons + rfl
- T8 (rowsLinearIndependent_generatorsList): **parametric** column-evaluation argument.
  Key idea: peel off f at each row by evaluating hf at one Z-column (extracts f 0) and one X-column (extracts f 1).
  ~60 LoC, harder than the [[4,2,2]] `by decide` but much cleaner than RepetitionN's approach.
- T10 (stabilizerGroup_toSubgroup_eq): standard.
- T11 (logicalX_anticommutes_logicalZ_diag): parametric `by_cases` on logIdx/xAnchor/zAnchor/else.
  Filter = {logIdx i}, cardinality 1, odd. Introduced 3 anchor-distinct helper lemmas.
- T12a (logicalX_commutes_logicalX): `commutes_of_componentwise_commutes` + split_ifs +
  `simp [PauliOperator.mulOp]`. Bypasses `pauli_comm_componentwise`'s `fin_cases i`.
- T12b (logicalZ_commutes_logicalZ): mirror of T12a.
- T12c (logicalX_commutes_logicalZ_offdiag for i ≠ j): split_ifs + simp_all on
  mulOp; ~20 LoC. The `simp_all` resolves all cases since the supports are
  fully disjoint (no shared qubit).
- T13-helpers (logicalX_commutes_S_Z, logicalX_commutes_S_X): one parametric
  filter (`{logIdx i, xAnchor m}`, count 2 even); one componentwise commute.
- T14-helpers (logicalZ_commutes_S_Z, logicalZ_commutes_S_X): mirror of T13-helpers.
- T13, T14 (logicalX/Z_mem_centralizer): standard `forall_comm_closure_iff` dispatch.
- T15 (stabilizerCode): structure literal — `logical_commute_cross` via
  structural `refine ⟨_, _, _, _⟩` consuming T12a/T12b/T12c + `by_cases`
  on `ℓ = ℓ'` (since `fin_cases ℓ <;> fin_cases ℓ'` is unavailable for
  parametric `Fin (2m − 2)`).
- T16 (stabilizerCode_toSubgroup_eq): `change` + `rw [listToSet_generatorsList]`.
- T17 (weight_one_anticomm_witness): clean 3-way `match P, hP`. No
  `hi_dichotomy` needed — both stabilizers have full support.
- weight_logicalX helper: parametric support computation, used by T18.
- T18 (code_has_distance_two): one-liner via
  `hasCodeDistance_two_of_anticommute_witness` (PR #34 helper).
- T19 (stabilizerCodeWithDistance): structure literal packaging.

### Cleanup (post-T19, agent killed mid-cleanup; spawning agent finished)

- 3 linter warnings on N.lean resolved:
  - Line 565: dropped unused `hza.symm` from `simp [hza.symm, PauliOperator.mulOp]`
  - Line 736: dropped unused `hxa.symm` from `simp [hxa.symm]`
  - Line 741: `show` → `change` (tactic actually rewrites the goal)
  - Line 486: `simp [logIdx]` → `simp only [logIdx]` (new `linter.flexible`
    site introduced post-cleanup; resolved before commit)
- Stage-2 baseline files committed alongside Stage-4 wrap-up (oversight:
  Stage 2 produced them in the worktree but didn't commit them):
  - `QEC/Stabilizer/Codes/Iceberg.lean` (family umbrella)
  - `pipeline/attempts/iceberg/{informal_spec, plan, reuse_audit, gap_audit}.md`
- `state.yaml`: `status` flipped `formalization → pr-ready`,
  `formalization_completed_at` set, `final_loc` recorded.
- `lake build` clean repo-wide (3341 jobs); no new linter warnings on the
  new file.

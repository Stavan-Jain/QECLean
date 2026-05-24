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


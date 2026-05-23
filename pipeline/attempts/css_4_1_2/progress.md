# Progress log: [[4,1,2]] LNCY code (`css_4_1_2`)

## Session 1 (2026-05-23)

- Starting sorries: **26** across 21 theorem statements (T1–T21).
- Budget: 8h, per-sorry 15min autoprove + 25min sorry-filler-deep.
- Plan order: T1 → T21 (per `plan.md` dependency graph).
- Reference template: `Codes/Small/FourQubit_4_2_2.lean` (same n, same CSS shape).

### Setup
- Worktree mathlib symlink verified.
- Skeleton `lake build` confirmed: 26 `declaration uses sorry` warnings, no errors.
- Proof approach: direct edits driven by the FourQubit_4_2_2 template
  (mechanical adaptation, k=1 vs k=2; 2 Z-generators vs 1).

### Batch 1 — T1 through T16 (typing, commutation, centralizer)

- **T1** (`ZGenerators_are_ZType`): closed by `rcases hg with rfl | rfl`,
  per-generator `fin_cases i <;> simp`. First attempt missed
  `NQubitPauliOperator.identity` in the simp set — Lean reported
  `NQubitPauliOperator.identity 4 2 = PauliOperator.I ∨ …` was unsolved.
  Added `NQubitPauliOperator.identity` to the simp lemmas; closed.
- **T2** (`XGenerators_are_XType`): same fix. (Note: later cleaned out
  the extra `NQubitPauliOperator.identity` here — `linter.unusedSimpArgs`
  flagged it because for X1 specifically all positions get overwritten by
  `.set`, so identity never appears in the residual goal.)
- **T3** (`S_Z1_comm_S_X1`): `pauli_comm_even_anticommutes` + filter
  `{0, 1}`. Decided via `decide`.
- **T4** (`S_Z2_comm_S_X1`): filter `{2, 3}`. Same pattern.
- **T5** (`generators_commute`): standard rcases dispatch, 4 cases
  (Z×Z, Z×X, X×Z, X×X) routing to `ZType_commutes`, `cross`,
  `XType_commutes.symm`. Verbatim from [[4,2,2]] except `Or.inl/Or.inr`
  on the 2-Z generator list.
- **T6** (`negIdentity_not_mem`): one-shot `CSS.negIdentity_not_mem_closure_union`.
- **T7** (`listToSet_generatorsList`): `simp only [...]` + `ext` + final
  `simp only`. First attempt failed because the list has 3 elements and
  `Set.mem_insert_iff` unfolds left-associated (`(a ∨ b) ∨ c`), whereas
  `Set.mem_union (ZGenerators ∪ XGenerators)` after `Set.mem_insert_iff`
  unfolds right-associated (`a ∨ (b ∨ c)`). Added `or_assoc` to the final
  simp set to close.
- **T8** (`AllPhaseZero_generatorsList`): nested
  `AllPhaseZero_cons.mpr ⟨rfl, ...⟩` × 3. Used the explicit `rw +
  refine ⟨rfl, ?_⟩` chain for clarity over the `simpa` shortcut.
- **T9** (`rowsLinearIndependent_generatorsList`): `by decide`.
- **T10** (`GeneratorsIndependent_4_generatorsList`): non-sorry — a term
  that uses T9 via `GeneratorsIndependent_of_rowsLinearIndependent` (in
  the skeleton already; no `sorry` to close).
- **T11** (`stabilizerGroup_toSubgroup_eq`): `simp only [...]` + `rw`.
- **T12** (`logicalX_anticommutes_logicalZ`): filter `{0}`,
  `pauli_anticomm_odd_anticommutes`.
- **T13a-c** (`logicalX_commutes_S_{Z1,Z2,X1}`):
  - vs S_Z1: filter `{0, 1}` (even).
  - vs S_Z2: `pauli_comm_componentwise` (no overlap with anticommute).
  - vs S_X1: `pauli_comm_componentwise` (both X-type).
- **T14a-c** (`logicalZ_commutes_S_{Z1,Z2,X1}`):
  - vs S_Z1: `pauli_comm_componentwise` (both Z-type).
  - vs S_Z2: `pauli_comm_componentwise` (both Z-type).
  - vs S_X1: filter `{0, 2}` (even).
- **T15, T16** (`logicalX/Z_mem_centralizer`):
  `StabilizerGroup.mem_centralizer_iff + forall_comm_closure_iff + rcases`.

**Status after batch 1**: 16/26 closed, 10 remaining. Commit `5a4238a`.

### Batch 2 — T17/T18 + T19 helpers + T19 witness + T20 + T21

- **T17** (`stabilizerCode`): non-sorry — structure literal already
  populated in the skeleton; the `logical_commute_cross` field uses
  `Subsingleton.elim` directly. Nothing to close here.
- **T18** (`stabilizerCode_toSubgroup_eq`): `change` + `rw`. Same as the
  [[4,2,2]] template, verbatim.
- **T19a** (`weightOneAt_anticomm_S_Z1`): the trick is that the filter
  equality has to incorporate the `hi : i = 0 ∨ i = 1` case-split inside
  the `ext` proof — at the call site we can't pick a specific concrete
  value for `i` since the lemma is universally quantified over `i`.
  Solution: do the `rcases hi <;> rcases hP` inside the filter-equality
  proof, between `ext j` and `fin_cases j`. The resulting case explosion
  (2 × 2 × 4 = 16 cases) is handled cleanly by `simp`.
- **T19b** (`weightOneAt_anticomm_S_Z2`): same shape, mirror of T19a.
- **T19c** (`weightOneAt_Z_anticomm_S_X1`): no `hi` constraint (Z·X
  anticommutes at every qubit), so the [[4,2,2]] template applies
  verbatim.
- **T19** (`weight_one_anticomm_witness`): match on `P, hP`:
  - `P = X` / `P = Y`: pick S_Z1 or S_Z2 by `i ∈ {0,1}` vs `i ∈ {2,3}`
    dichotomy. Initial draft used `by_cases hi : i = 0 ∨ i = 1` per branch;
    a small refactor pulled out the dichotomy as a single
    `have hi_dichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3)` (closed by
    `fin_cases i <;> tauto`) reused across `X` and `Y` branches.
  - `P = Z`: pick S_X1.
  - `P = I`: contradiction from `hP : P ≠ I`.
- **T20** (`code_has_distance_two`): verbatim from [[4,2,2]] using
  `hasCodeDistance_of` + `IsNontrivialLogicalOperator_iff` +
  `no_weight_one_mem_centralizer_of_anticommute_witness`. The
  `(logicalOpsCSS_4_1_2 0).xOp_nontrivial` invocation gives the
  weight-2 logicalX witness directly.
- **T21** (`stabilizerCodeWithDistance`): non-sorry — structure literal
  bundling T17 + T20.

**Cleanup pass**: two `linter.unusedSimpArgs` warnings flagged the
unused `NQubitPauliOperator.identity` simp argument in T2 and T19c
(the simp set normalizes via `.set` chains, which fully overwrite the
identity for those theorems). Removed both arguments — file now compiles
with zero warnings.

**Final whole-repo `lake build`**: clean, all 3422 jobs succeed. No new
warnings introduced anywhere.

**Status after batch 2**: 26/26 sorries closed (21/21 theorem
statements). 0 BLOCKED. Final LoC = 505. Ready for PR.

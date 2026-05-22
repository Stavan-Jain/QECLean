# Progress: stab_4_2_2

## Session 1 (2026-05-22)

- Starting sorries: 22
- Budget: 8h, per-sorry 15min autoprove + 25min sorry-filler-deep
- Plan order: T1, T2, T3a, T3, T4, T5, T6a (listToSet), T6b (rowsIndep), T6c (toSubgroup_eq), T7, T8a, T8b, T9a, T9b, T9c, T9d, T10a, T10b, T11a, T11b, T12, T13

### Closed (22/22)
- **T1 ZGenerators_are_ZType**: `rcases hg with rfl` + `refine ⟨rfl, ?_⟩` + `fin_cases i <;> simp`. Closed directly.
- **T2 XGenerators_are_XType**: analogous to T1. Closed directly.
- **T3a Z1_comm_X1**: `pauli_comm_even_anticommutes` + hfilter = `{0,1,2,3}` (Steane7:136 pattern). Closed directly.
- **T3 ZGenerators_commute_XGenerators**: `rcases` singletons + `Z1_comm_X1`. Closed directly.
- **T4 generators_commute**: union case-split → `ZType_commutes`/`XType_commutes`/`ZGenerators_commute_XGenerators` (Steane7:260 pattern).
- **T5 negIdentity_not_mem**: `CSS.negIdentity_not_mem_closure_union` (Steane7:277 pattern).
- **T6a listToSet_generatorsList**: `simp only [generatorsList, generators, …] + ext` (Steane7:290 pattern, two-element list).
- **T7 AllPhaseZero_generatorsList**: nested `AllPhaseZero_cons` (Steane7:320 pattern, two `cons` cases only).
- **T6b rowsLinearIndependent_generatorsList**: `decide` over the 2x8 check matrix. Closed.
- **T6c stabilizerGroup_toSubgroup_eq**: `simp only + rw [listToSet_generatorsList]` (Steane7:307 pattern).
- **T8a logicalX_1_anticommutes_logicalZ_1**: `pauli_anticomm_odd_anticommutes` + hfilter = `{3}` (cardinality 1, odd). Closed.
- **T8b logicalX_2_anticommutes_logicalZ_2**: same pattern, hfilter = `{3}`. Closed.
- **T9a logicalX_1_commutes_logicalX_2**: `pauli_comm_componentwise` (both X-type).
- **T9b logicalX_1_commutes_logicalZ_2**: hfilter = `{1,3}` (cardinality 2, even).
- **T9c logicalX_2_commutes_logicalZ_1**: hfilter = `{2,3}`.
- **T9d logicalZ_1_commutes_logicalZ_2**: `pauli_comm_componentwise` (both Z-type).
- **T10a logicalX_1_mem_centralizer**: Steane7:413 pattern, two helper lemmas (vs. Z1: hfilter={1,3}; vs. X1: componentwise).
- **T10b logicalX_2_mem_centralizer**: hfilter={2,3} vs. Z1; componentwise vs. X1.
- **T11a logicalZ_1_mem_centralizer**: componentwise vs. Z1; hfilter={2,3} vs. X1.
- **T11b logicalZ_2_mem_centralizer**: componentwise vs. Z1; hfilter={1,3} vs. X1.
- **T12 logical_commute_cross**: `fin_cases ℓ <;> fin_cases ℓ'` with `(ℓ, ℓ') ∈ {(0,0), (1,1)}` closed by `(hne rfl).elim`, and `(0,1), (1,0)` closed by `refine ⟨T9a, T9b, T9c.symm, T9d⟩` and `.symm` variants. **No `Subsingleton.elim` shortcut — first true k=2 instance in the repo.**
- **T13 code_has_distance_two**: Used `hasCodeDistance_of` with d=2:
  - `hd`: `by decide` (`2 ≥ 1`).
  - `h_witness`: `logicalX_1, (logicalOps4_2_2 0).xOp_nontrivial, by decide` (weight = 2 by decide).
  - `h_min`: `interval_cases w` collapses to `w = 1`, then `no_weight_one_mem_centralizer_of_anticommute_witness` (from `Core/CSSDistance.lean` — pre-existing, previously unused, found via reuse audit follow-up). The witness function exhibits Z1 for X/Y and X1 for Z at each qubit. **This pre-existing helper was the entire ballgame for T13** — without it, we would have enumerated 12 cases manually.

### Linter cleanups applied
- Replaced `simp [generators] at hs` (`linter.flexible`) with `simp only [generators, Set.mem_union] at hs` via `simp?` MCP suggestion (4 sites).
- Trimmed unused `NQubitPauliOperator.identity` simp args after `lake build` flagged `linter.unusedSimpArgs` (3 sites + 4 more inside T13 helpers).
- Replaced `show (mkStabilizerFromGenerators ...).toSubgroup = _` with `change ...` (`linter.style.show`).
- `rw [hfilter]; decide` → `rw [hfilter]; simp +decide` for the `({i} : Finset (Fin 4)).card` goals to dodge the "expected type must not contain free variables" `decide` trap.

### Final stats
- 22/22 sorries closed.
- 0 BLOCKED.
- `lake build` clean (no errors, no warnings).
- Final LoC: 547 (vs. estimated 300 — overrun explained by the T13 witness helpers and explicit 8-lemma centralizer-helper expansion which Steane7's k=1 shortcut hides).
- Wall-clock: well under 2 hours (no escalations needed; the Steane7 template translated cleanly).
- Subagent delegations: 0 (proofs were direct adaptations of Steane7 patterns; no `lean4:autoprove` or `lean4:sorry-filler-deep` invocations needed).

### Golf pass
- Factored `weight_one_anticomm_witness` into two reusable helper lemmas (`weightOneAt_anticomm_Z1`, `weightOneAt_Z_anticomm_X1`); ~2 LoC saved, but the main win is clarity.

# Result: `iceberg` — `[[2m, 2m − 2, 2]]` parametric family

## Status

**pr-ready** — all 24 sorries closed, `lake build` clean repo-wide, zero
linter warnings on the new file, zero `BLOCKED` markers.

## Sorries closed

24 of 24 (T1–T19 with 5 helper sub-labels). First parametric small CSS
detection code in the repo.

| ID | Theorem | Closing tactic (parametric specifics in **bold**) |
|----|---------|----------------|
| T1 | `ZGenerators_are_ZType` | direct unfold; per-qubit constant Z |
| T2 | `XGenerators_are_XType` | mirror of T1 |
| T3 | `S_Z_comm_S_X` | `pauli_comm_even_anticommutes` + filter = `Finset.univ`; **cardinality `2m`, even via `⟨m, by ring⟩`** |
| T3-bundle | `ZGenerators_commute_XGenerators` | `rcases` on singletons + T3 |
| T4 | `generators_commute` | 4-way `rcases` dispatch via Z/X-type commutes + T3 |
| T5 | `negIdentity_not_mem` | `CSS.negIdentity_not_mem_closure_union` one-liner |
| T6 | `listToSet_generatorsList` | direct simp on `Set` extensionality |
| T7 | `AllPhaseZero_generatorsList` | chain `AllPhaseZero_cons` + `rfl` |
| T8 | `rowsLinearIndependent_generatorsList` | **column-evaluation argument over parametric `m`**: peel off `f` at each row by evaluating `hf` at one Z-column and one X-column. ~60 LoC. Replaces the [[4,2,2]] `by decide` (which doesn't work parametrically) |
| T10 | `stabilizerGroup_toSubgroup_eq` | standard |
| T11 | `logicalX_anticommutes_logicalZ_diag` | **parametric `by_cases` on `logIdx`/`xAnchor`/`zAnchor`/else** (4-way) |
| T12a | `logicalX_commutes_logicalX` | `commutes_of_componentwise_commutes` + `split_ifs` + `simp [PauliOperator.mulOp]`. **Bypasses `pauli_comm_componentwise`'s `fin_cases i`** which doesn't work for parametric `Fin (2m)` |
| T12b | `logicalZ_commutes_logicalZ` | mirror of T12a |
| T12c | `logicalX_commutes_logicalZ_offdiag` (i ≠ j) | `split_ifs` + `simp_all` on `mulOp`; supports fully disjoint |
| T13-helper-XZ | `logicalX_commutes_S_Z` | parametric filter `{logIdx i, xAnchor m}`, count 2 even |
| T13-helper-XX | `logicalX_commutes_S_X` | componentwise commute (both X-type) |
| T14-helper-ZZ | `logicalZ_commutes_S_Z` | componentwise commute (both Z-type) |
| T14-helper-ZX | `logicalZ_commutes_S_X` | mirror of T13-helper-XZ |
| T13 | `logicalX_mem_centralizer` | `mem_centralizer_iff` + `forall_comm_closure_iff` + `rcases` |
| T14 | `logicalZ_mem_centralizer` | same shape |
| T15 | `stabilizerCode` | structure literal — `logical_commute_cross` field consumes T12a/T12b/T12c via a **structural `refine ⟨_, _, _, _⟩`** because `fin_cases ℓ <;> fin_cases ℓ'` is unavailable on parametric `Fin (2m - 2)` |
| T16 | `stabilizerCode_toSubgroup_eq` | `change` + `rw [listToSet_generatorsList]` |
| T17 | `weight_one_anticomm_witness` | **3-way `match P, hP`** — clean dispatch: X- or Y-anchored Pauli at any qubit anticomms with `S_Z m`; Z-anchored Pauli at any qubit anticomms with `S_X m`. **No `hi_dichotomy` needed** (the all-X / all-Z stabilizers cover every qubit, simpler than CSS_4_1_2.lean's two-Z-gen case) |
| weight_logicalX (T18 helper) | weight = 2 | parametric support computation: `{logIdx i, xAnchor m}` with `Finset.card_insert_of_notMem` |
| T18 | `code_has_distance_two` | **`hasCodeDistance_two_of_anticommute_witness`** (PR #34 helper) with `⟨logicalX m ⟨0, h0lt⟩, xOp_nontrivial, weight_logicalX⟩` |
| T19 | `stabilizerCodeWithDistance` | structure literal |

## Blocked sorries

**None.** Per `gap_audit.md`'s prediction.

## Lines of Lean produced

**Final LoC**: 765 (estimate: 500; final is 53% above estimate — typical for
the first instance of a new pattern, here the parametric column-evaluation
argument for T8 and the structural-`refine` workaround for T15).

The over-shoot is concentrated in:
- T8 column-evaluation argument (~60 LoC vs ~5 for `by decide` in the
  m=2 instance — the cost of going parametric)
- T11 4-way `by_cases` on logIdx/xAnchor/zAnchor/else (~25 LoC)
- T13-helper-XZ filter equality (~20 LoC) — re-used for T14-helper-ZX
- weight_logicalX support computation (~22 LoC)
- T15 structural `refine` for `logical_commute_cross` (~20 LoC vs the
  4-line `fin_cases ℓ <;> fin_cases ℓ'` in the m=2 instance)

The remaining proofs are direct parametric ports of the
`FourQubit_4_2_2.lean` template.

## Time spent

| Phase | Wall-clock |
|-------|------------|
| Setup, parse check, plan study | ~10 min |
| Batch 1 (T1–T8) | ~30 min |
| Batch 2 (T10–T14) | ~30 min |
| Batch 3 (T15–T19, uncommitted at first interrupt) | ~25 min |
| Linter cleanup (3 warnings: unused simp args on lines 565, 736; show→change on 741; simp→simp only on 486) | ~5 min |
| Result write-up + state finalization | ~5 min |
| **Total** | **~1h 45min** |

Well under the 8-hour budget. The Stage-4 agent was killed mid-cleanup
(after closing all 24 sorries but before fixing the 3 linter warnings
and committing the T15–T19 batch); the spawning agent finalized the
cleanup, committed, and authored this write-up.

## Patterns discovered

These are candidates for the next CLAUDE.md update (Stage 6 post-merge).

1. **Parametric column-evaluation arguments for `rowsLinearIndependent`**.
   When the check-matrix dimension is parametric (e.g., `(n − k) × n` with
   `n = 2m`, `n − k = 2`), the `by decide` approach used for concrete-`m`
   codes fails. The clean parametric pattern is to peel off each row of `f`
   by evaluating `hf` at carefully chosen columns:

   ```lean
   -- T8 in iceberg/N.lean:
   intro f hf
   have h0 : f 0 = 0 := by
     have := congrFun hf (Sum.inl 0)  -- evaluate at the first Z-column
     -- the row-sum reduces to f 0 * 1 + f 1 * 0 = f 0
     simpa [...] using this
   have h1 : f 1 = 0 := by
     have := congrFun hf (Sum.inr 0)  -- evaluate at the first X-column
     simpa [...] using this
   ext i; fin_cases i <;> [exact h0; exact h1]
   ```

   Generalizes to any small CSS code where the natural check matrix has
   "single-block" rows (a Z-row covering some columns + an X-row covering
   the complementary columns).

2. **Bypassing `fin_cases ℓ <;> fin_cases ℓ'` for parametric `Fin n`**:
   The `pauli_comm_componentwise` tactic and `logical_commute_cross`
   field of `StabilizerCode` both want to enumerate over `Fin (2m − 2)`,
   which `fin_cases` can't do symbolically. The clean workaround is to
   *structurally* decompose the `∀ ℓ ℓ', ...` into the `i = j` and `i ≠ j`
   sub-cases via `by_cases` and `Decidable.em`, then dispatch each case
   to a previously-proved lemma (T12a/T12b/T12c here):

   ```lean
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro ℓ ℓ'; exact logicalX_commutes_logicalX m ℓ ℓ'        -- T12a
   · intro ℓ ℓ'; exact logicalZ_commutes_logicalZ m ℓ ℓ'        -- T12b
   · intro ℓ ℓ' hℓℓ'                                            -- T12c
     by_cases hij : ℓ = ℓ'
     · exact absurd hij hℓℓ'
     · exact logicalX_commutes_logicalZ_offdiag m ℓ ℓ' hij
   · ...
   ```

3. **`linter.flexible` on parametric `simp [logIdx] at this`**: when the
   `simp` is just unfolding an `@[inline] private def`, replace with
   `simp only [logIdx] at this`. The narrower form satisfies the linter
   and (with `@[inline]`) reduces identically.

4. **No `hi_dichotomy` needed when all generators cover every qubit**.
   The CSS_4_1_2 multi-Z anti-witness pattern (with `hi_dichotomy` over
   `{0, 1} ∨ {2, 3}`) is overkill when both stabilizers have full
   support. For iceberg's `weight_one_anticomm_witness`, a plain 3-way
   `match P, hP` over `{X, Y, Z}` suffices — much simpler.

## Suggested follow-ups (not blocking)

1. **`Foundations` lemma `allX_allZ_commute_of_even`**. The T3 closing
   pattern (`pauli_comm_even_anticommutes` + filter = `Finset.univ` +
   parity via `⟨m, by ring⟩`) is the kind of small algebraic fact that
   could live in `Foundations/PauliGroup/CommutationLemmas.lean` (or
   wherever `pauli_comm_even_anticommutes` lives). Defer until a second
   instance needs it (e.g., a future code with all-Y stabilizers).

2. **Generalize `hasCodeDistance_two_of_anticommute_witness` to
   `hasCodeDistance_three_of_anticommute_witness`**. Distance-3 codes
   would chain the existing `no_weight_one_*` and `no_weight_two_*`
   helpers. Defer until a third distance-3 code lands (currently we
   have `FiveQubit_5_1_3.lean`).

3. **`stab_6_4_2`** ([[6, 4, 2]], composite 8.10, rank 5) is the m=3
   instance of this iceberg formalization. Should be marked `done` in
   the next re-scoring pass (parametric coverage), and a `patch_scoring.py`
   correction added if the prioritizer doesn't auto-detect.

4. **No catalog gaps to file.** Every dependency was available; no
   mathlib API drift; no v4.30 idioms broken. PR #34's helper landed
   exactly as predicted by `gap_audit.md`.

5. **Move `[[2m, 2m-2, 2]]` (and small instances [[6,4,2]], [[8,6,2]], etc.)
   to the catalog's `Done` set**. Edit `state.yaml` to `status: pr-ready`
   here; catalog re-score (advisory) at next batch will pick up the auto-
   coverage of small-m instances.

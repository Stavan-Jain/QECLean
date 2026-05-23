# Result: `css_4_1_2` — [[4,1,2]] LNCY code

## Status

**pr-ready** — all 26 sorries closed, `lake build` clean repo-wide, zero
linter warnings on the new file, zero `BLOCKED` markers.

## Sorries closed

26 of 26 (21 of 21 theorem statements).

| ID | Theorem | Closing tactic |
|----|---------|----------------|
| T1 | `ZGenerators_are_ZType` | `rcases hg` + `fin_cases i` + `simp [PauliOperator.IsZType, S_Z{1,2}, .set, .identity]` |
| T2 | `XGenerators_are_XType` | `rcases hg` + `fin_cases i` + `simp [PauliOperator.IsXType, S_X1, .set]` |
| T3 | `S_Z1_comm_S_X1` | `pauli_comm_even_anticommutes`, filter = `{0, 1}` |
| T4 | `S_Z2_comm_S_X1` | `pauli_comm_even_anticommutes`, filter = `{2, 3}` |
| T5 | `generators_commute` | `rcases` + dispatch to `ZType_commutes`/cross/`XType_commutes` |
| T6 | `negIdentity_not_mem` | `CSS.negIdentity_not_mem_closure_union` one-liner |
| T7 | `listToSet_generatorsList` | `simp only [...]` + `ext` + `simp only [..., or_assoc]` |
| T8 | `AllPhaseZero_generatorsList` | nested `AllPhaseZero_cons.mpr ⟨rfl, …⟩` × 3 |
| T9 | `rowsLinearIndependent_generatorsList` | `by decide` |
| T10 | `GeneratorsIndependent_4_generatorsList` | (already a term in the skeleton; no sorry) |
| T11 | `stabilizerGroup_toSubgroup_eq` | `simp only [...]` + `rw [listToSet_generatorsList]` |
| T12 | `logicalX_anticommutes_logicalZ` | `pauli_anticomm_odd_anticommutes`, filter = `{0}` |
| T13a | `logicalX_commutes_S_Z1` | `pauli_comm_even_anticommutes`, filter = `{0, 1}` |
| T13b | `logicalX_commutes_S_Z2` | `pauli_comm_componentwise [logicalX, S_Z2]` (no overlap) |
| T13c | `logicalX_commutes_S_X1` | `pauli_comm_componentwise [logicalX, S_X1]` (both X) |
| T14a | `logicalZ_commutes_S_Z1` | `pauli_comm_componentwise [logicalZ, S_Z1]` (both Z) |
| T14b | `logicalZ_commutes_S_Z2` | `pauli_comm_componentwise [logicalZ, S_Z2]` (both Z) |
| T14c | `logicalZ_commutes_S_X1` | `pauli_comm_even_anticommutes`, filter = `{0, 2}` |
| T15 | `logicalX_mem_centralizer` | `mem_centralizer_iff` + `forall_comm_closure_iff` + `rcases` |
| T16 | `logicalZ_mem_centralizer` | same shape |
| T17 | `stabilizerCode` | (structure literal in skeleton; non-sorry) |
| T18 | `stabilizerCode_toSubgroup_eq` | `change` + `rw [listToSet_generatorsList]` |
| T19a | `weightOneAt_anticomm_S_Z1` | filter `= {i}` with `rcases hi <;> rcases hP` inside the filter-eq proof |
| T19b | `weightOneAt_anticomm_S_Z2` | same |
| T19c | `weightOneAt_Z_anticomm_S_X1` | filter `= {i}`, no `hi` constraint |
| T19 | `weight_one_anticomm_witness` | `match P, hP` + `hi_dichotomy` reusable across `X`/`Y` branches |
| T20 | `code_has_distance_two` | `hasCodeDistance_of` + `no_weight_one_mem_centralizer_of_anticommute_witness` |
| T21 | `stabilizerCodeWithDistance` | (structure literal in skeleton; non-sorry) |

## Blocked sorries

**None.** Per `gap_audit.md`'s prediction, zero blockers materialized.

## Lines of Lean produced

**Final LoC**: 505 (original estimate: 300; final is 68% above estimate).

The 200-line over-shoot is concentrated in:
- T1 (24 lines for the 2-generator Z-type proof vs ~12 in `FourQubit_4_2_2.lean`'s 1-generator version),
- T19a / T19b (12 lines × 2 = 24 lines of helper machinery for the new
  Z-generator dichotomy — `FourQubit_4_2_2.lean` had only one Z-gen so
  needed neither a Z1 nor Z2 helper),
- T19 witness (16 lines vs ~8 in `FourQubit_4_2_2.lean` because of the
  `hi_dichotomy` case-split between `S_Z1` and `S_Z2`).

The remaining proofs are essentially line-for-line ports from the
[[4,2,2]] template.

## Time spent

| Phase | Wall-clock |
|-------|------------|
| Setup (symlink verify, read metadata, skeleton parse check) | ~5 min |
| Batch 1 (T1–T16) drafting + iteration | ~20 min |
| Batch 1 build + fix (T1, T2 missing `identity`; T7 `or_assoc`) | ~8 min |
| Batch 2 (T18–T20) drafting | ~10 min |
| Build + cleanup (T19 simplify, linter fixes, doc-comment update) | ~10 min |
| Whole-repo verification + write-up | ~5 min |
| **Total** | **~1 hour** |

Well under the 8-hour budget; the proofs are unusually mechanical because
this is essentially the [[4,2,2]] code with one extra Z-generator.

## Patterns discovered

These are candidates for the next CLAUDE.md update (`v4.30 patterns` or
the `Linter-clean idioms` section). None are surprising in isolation,
but several are first-time occurrences in the repo.

1. **Multi-Z-generator anti-witness functions**: when a CSS code has more
   than one Z-stabilizer, the weight-1 X/Y anti-witness function must
   dispatch on which qubits the local Z-stab covers. The clean idiom is

   ```lean
   have hi_dichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) := by
     fin_cases i <;> tauto
   ```

   re-used across the `P = X` and `P = Y` branches, vs. doing
   `by_cases` inline in each branch (which duplicates the dichotomy
   case-split). This generalizes immediately to larger CSS codes
   (e.g. the next iceberg-family code).

2. **The `hi`-conditional filter-equality pattern** (T19a, T19b): when a
   helper lemma is universally quantified over `i : Fin n` but
   constrained to `i ∈ S` for some subset `S` (here, `{0, 1}` or
   `{2, 3}`), the filter equality

   ```lean
   have hfilter :
       (Finset.univ.filter (anticommutesAt ...)) = ({i} : Finset (Fin 4)) := by
     ext j; rcases hi with rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
       simp [...]
   ```

   does the `rcases` over `hi` and `hP` *inside* the `ext` proof,
   before `fin_cases j`. This avoids having to specialize the lemma
   statement (which would require a non-universal `i`, defeating the
   purpose). The case multiplication (2 hi-cases × 2 hP-cases × 4 j-cases
   = 16) is dispatched cleanly by `simp` at the leaves.

3. **`or_assoc` in 3-element list-to-set proofs**: the `listToSet
   generatorsList = generators` proof works for `len ≤ 2` lists via the
   stock simp set `[Set.mem_insert_iff, Set.mem_union, …]`, but at
   `len = 3` (or more, when the set is structured as
   `{Z1, Z2} ∪ {X1}`), the left-associated `(a ∨ b) ∨ c` from
   `Set.mem_insert_iff` doesn't match the right-associated
   `a ∨ (b ∨ c)` from `Set.mem_union`. Adding `or_assoc` to the simp
   set bridges them. Worth adding to CLAUDE.md if a third example
   surfaces.

4. **Linter-clean: `linter.unusedSimpArgs` on `NQubitPauliOperator.identity`**:
   when a `.set` chain *fully covers* all `Fin n` positions (e.g. `S_X1`
   sets all 4 qubits to X), the underlying `NQubitPauliOperator.identity`
   never appears in the residual goals after `fin_cases` — and the
   linter correctly flags it as an unused simp argument. For partial
   coverage (e.g. `S_Z1` sets only qubits 0 and 1), `identity` *is*
   needed for the un-set positions. Rule of thumb: drop `identity` from
   the simp set when every qubit is set; keep it otherwise. The linter
   tells you which.

## Suggested follow-ups

1. **Consider lifting a `CSS.distance_two_of_anticomm_witness` helper**.
   The T20 closing pattern (`hasCodeDistance_of` + `interval_cases w` +
   `no_weight_one_mem_centralizer_of_anticommute_witness`) is now
   duplicated verbatim between `FourQubit_4_2_2.lean` and
   `CSS_4_1_2.lean`. If a third small distance-2 CSS code lands (the
   iceberg family `[[2m, 2m-2, 2]]` is queued), promoting this five-line
   ritual to a one-call helper in `Framework/Core/CSS/CSSDistance.lean`
   would save ~15 lines per code. **Not blocking** — flagged by
   `gap_audit.md` and confirmed during this attempt.

2. **The 2-Z anti-witness helper pattern (T19a-c + T19) is a candidate
   for a generic CSS-distance toolkit.** For an arbitrary CSS code with
   multiple Z-generators whose supports partition `Fin n`, the
   "weight-1 X/Y at qubit `i` anticommutes with whichever Z-generator
   covers `i`" lemma is purely a function of the support partition.
   A generic helper

   ```lean
   lemma weightOneAt_XY_anticomm_some_Zgen (n) (Zgens : List (NQubitPauliGroupElement n))
     (cover : ∀ i, ∃ g ∈ Zgens, IsZType g ∧ g.operators i ≠ I) :
     ∀ i, ∀ P ∈ {X, Y}, ∃ g ∈ Zgens, Anticommute (weightOneAt i P) g
   ```

   would centralize this. Not justified by one new code; revisit at the
   third instance.

3. **Move the `[[4,1,2]]` entry to the catalog's `Done` set**. The
   pipeline dashboard reads `pipeline/queue.md` and the per-code
   `state.yaml`; flipping `status: skeleton-review → pr-ready` here is
   sufficient. Catalog re-score (advisory) at the next batch.

4. **No catalog gaps to file.** Every dependency was available; no
   mathlib API drift was hit; no v4.30 idioms were broken. The
   [[4,1,2]] LNCY is exactly the "second exerciser" of the CSS-detection
   path that `gap_audit.md` predicted, with no surprises.

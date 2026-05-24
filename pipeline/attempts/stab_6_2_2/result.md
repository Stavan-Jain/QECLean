# Result: stab_6_2_2

## Status

**pr-ready** — all 47 sorries closed, `lake build` clean repo-wide, no
warnings or info notices on `QEC/Stabilizer/Codes/Small/SixQubit_6_2_2.lean`.

## Sorries closed (47 / 47)

| Theorem | Description | Closing tactic |
|---------|-------------|----------------|
| T1 | `ZGenerators_are_ZType` | `rcases` + `fin_cases i` + `simp [PauliOperator.IsZType, S_Z*, ...]` |
| T2 | `XGenerators_are_XType` | analogous to T1 with `IsXType` / `S_X*` |
| T3 | `S_Z1 * S_X1 = S_X1 * S_Z1` (overlap {0,1,2,3}) | `pauli_comm_even_anticommutes` + Finset.ext + `decide` on cardinality |
| T4 | `S_Z1 * S_X2 = S_X2 * S_Z1` (overlap {0,1}) | same as T3 |
| T5 | `S_Z2 * S_X1 = S_X1 * S_Z2` (overlap {0,1}) | same as T3 |
| T6 | `S_Z2 * S_X2 = S_X2 * S_Z2` (overlap {0,1,4,5}) | same as T3 |
| T7 | `ZGenerators_commute_XGenerators` | 4-way `rcases` over T3-T6 |
| T8 | `generators_commute` (all-pair) | CSS structural argument via `CSSCommutationLemmas` |
| T9 | `negIdentity_not_mem` | one-shot via `CSS.negIdentity_not_mem_closure_union` |
| T10 | `listToSet_generatorsList` | `simp only` + `ext` + `simp only [Set.mem_*, or_assoc]` |
| T11 | `AllPhaseZero_generatorsList` | 4-level nested `⟨rfl, ...⟩` chain |
| T12 | `rowsLinearIndependent_generatorsList` | `by decide` (4×12 GF(2) matrix) |
| T13 | `GeneratorsIndependent_6_generatorsList` | derived from T12 (already structural) |
| T14 | `stabilizerGroup_toSubgroup_eq` | `simp only` + `rw [listToSet_generatorsList]` |
| T15 | `logicalX_1 ⊥ logicalZ_1` (overlap {3}) | `pauli_anticomm_odd_anticommutes` + Finset.ext + `decide` |
| T16 | `logicalX_2 ⊥ logicalZ_2` (overlap {4}) | same as T15 |
| T17 | `X̄_1 * X̄_2 = X̄_2 * X̄_1` (both X-type) | `pauli_comm_componentwise [logicalX_1, logicalX_2]` |
| T18 | `X̄_1 * Z̄_2 = Z̄_2 * X̄_1` (disjoint supports) | `pauli_comm_componentwise [logicalX_1, logicalZ_2]` |
| T19 | `X̄_2 * Z̄_1 = Z̄_1 * X̄_2` (overlap {3,4}) | `pauli_comm_even_anticommutes` + Finset.ext + `decide` |
| T20 | `Z̄_1 * Z̄_2 = Z̄_2 * Z̄_1` (both Z-type) | `pauli_comm_componentwise [logicalZ_1, logicalZ_2]` |
| T21a | `X̄_1 * S_Z1 = S_Z1 * X̄_1` (overlap {2,3}) | `pauli_comm_even_anticommutes` + filter |
| T21b | `X̄_1 * S_Z2 = S_Z2 * X̄_1` (disjoint) | `pauli_comm_componentwise` |
| T21c | `X̄_1 * S_X1 = S_X1 * X̄_1` (both X-type) | `pauli_comm_componentwise` |
| T21d | `X̄_1 * S_X2 = S_X2 * X̄_1` (both X-type) | `pauli_comm_componentwise` |
| T22a | `X̄_2 * S_Z1 = S_Z1 * X̄_2` (overlap {1,3}) | `pauli_comm_even_anticommutes` + filter |
| T22b | `X̄_2 * S_Z2 = S_Z2 * X̄_2` (overlap {1,4}) | `pauli_comm_even_anticommutes` + filter |
| T22c | `X̄_2 * S_X1 = S_X1 * X̄_2` (both X-type) | `pauli_comm_componentwise` |
| T22d | `X̄_2 * S_X2 = S_X2 * X̄_2` (both X-type) | `pauli_comm_componentwise` |
| T23a | `Z̄_1 * S_Z1 = S_Z1 * Z̄_1` (both Z-type) | `pauli_comm_componentwise` |
| T23b | `Z̄_1 * S_Z2 = S_Z2 * Z̄_1` (both Z-type) | `pauli_comm_componentwise` |
| T23c | `Z̄_1 * S_X1 = S_X1 * Z̄_1` (overlap {0,3}) | `pauli_comm_even_anticommutes` + filter |
| T23d | `Z̄_1 * S_X2 = S_X2 * Z̄_1` (overlap {0,4}) | `pauli_comm_even_anticommutes` + filter |
| T24a | `Z̄_2 * S_Z1 = S_Z1 * Z̄_2` (both Z-type) | `pauli_comm_componentwise` |
| T24b | `Z̄_2 * S_Z2 = S_Z2 * Z̄_2` (both Z-type) | `pauli_comm_componentwise` |
| T24c | `Z̄_2 * S_X1 = S_X1 * Z̄_2` (disjoint) | `pauli_comm_componentwise` |
| T24d | `Z̄_2 * S_X2 = S_X2 * Z̄_2` (overlap {4,5}) | `pauli_comm_even_anticommutes` + filter |
| T25 | `logicalX_1 ∈ centralizer` | `mem_centralizer_iff` + `forall_comm_closure_iff` + 4-way dispatch (T21a-d) |
| T26 | `logicalX_2 ∈ centralizer` | analogous via T22a-d |
| T27 | `logicalZ_1 ∈ centralizer` | analogous via T23a-d |
| T28 | `logicalZ_2 ∈ centralizer` | analogous via T24a-d |
| T29 | `StabilizerCode 6 2` packaging | `fin_cases ℓ <;> fin_cases ℓ'` 4-case dispatch for `logical_commute_cross` |
| T30 | `stabilizerCode_toSubgroup_eq` | `change` + `rw [listToSet_generatorsList]` |
| T31a | `weightOneAt_anticomm_S_Z1` (4-disj hi) | `pauli_anticomm_odd_anticommutes` + 4-way `rcases hi` + `fin_cases j` + `simp` |
| T31b | `weightOneAt_anticomm_S_Z2` (4-disj hi) | analogous to T31a |
| T31c | `weightOneAt_Z_anticomm_S_X1` (4-disj hi) | analogous to T31a (no `hP` since P=Z is fixed) |
| T31d | `weightOneAt_Z_anticomm_S_X2` (4-disj hi) | analogous to T31a (no `hP`) |
| T31 (main) | `weight_one_anticomm_witness` | 3-way `hi_trichotomy` + `match P, hP with` over X/Y/Z, dispatching to T31a-d |
| T32 | `code_has_distance_two` | one-line `hasCodeDistance_two_of_anticommute_witness` with `⟨logicalX_1, _, by decide⟩` |
| T33 | `stabilizerCodeWithDistance` | structure literal bundling T29 + T32 |

## Blocked sorries

**None.** All 47 sorries closed cleanly.

## Lines of Lean produced

- **Final**: 805 LoC (`SixQubit_6_2_2.lean`)
- **Stage-2 skeleton baseline**: 609 LoC
- **Net additions during Stage 4**: ~196 LoC (entirely proof content)
- **Original estimate (plan.md)**: ~500 LoC
- **Comparison to templates**: CSS_4_1_2 = 499 LoC (k=1, 3 generators); FourQubit_4_2_2 = 546 LoC (k=2, 2 generators, single-Z-stab single-X-stab). C_6 is naturally larger due to combining both axes of complexity: k=2 logicals (4 logicals × 4 generators = 16 commutation lemmas, vs CSS_4_1_2's 2×3 = 6, vs FourQubit_4_2_2's 4×2 = 8) plus 4 weight-1 anticommute helpers (vs CSS_4_1_2's 3, vs FourQubit_4_2_2's 2). The 805 LoC count tracks linearly with these combinatorics.

## Time spent

- **Pre-flight check** (read metadata, baseline build): ~5 min
- **T1-T14** (Z-type, X-type, cross-commute, generator list infra): ~10 min — direct adaptation of CSS_4_1_2 patterns
- **T15-T29** (logicals + centralizer + StabilizerCode): ~15 min — blend of CSS_4_1_2 + FourQubit_4_2_2 patterns; the 16 logical-vs-stab lemmas + the 4-way `fin_cases` cross-commute were the bulk of the LoC
- **T30, T31a-d, T31, T32**: ~10 min — the 4 helpers + 3-way trichotomy main witness were the most novel, but followed the documented CSS_4_1_2 + plan.md sketch line-by-line
- **Final build + result.md**: ~5 min
- **Total wall-clock**: ~45 min (well under the 8h cap)

## Patterns discovered

These would be worth adding to `docs/lean-patterns.md` (not CLAUDE.md per
the new tier rule):

### 1. Trichotomy extension of `hi_dichotomy` for multi-Z-stab CSS codes

The CSS_4_1_2 pattern documented in `docs/lean-patterns.md` uses a 2-way
`hi_dichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3)` because its two
Z-stabilizers cover disjoint qubit subsets {0,1} and {2,3}. C_6's
Z-stabilizers **overlap** at {0,1} and disagree at {2,3} (only S_Z1)
and {4,5} (only S_Z2), giving a non-disjoint 3-way partition.

The Lean pattern that handles the overlap is:

```lean
have hi_trichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5) := by
  fin_cases i <;> tauto
```

Then for the {0,1} branch (where both stabilizers cover), pick **either**
canonically (we pick S_Z1) and apply the helper with the **broader**
4-disjunction `i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3` (the support of S_Z1):

```lean
· -- i ∈ {0,1}: pick S_Z1 (also covers).
  refine ⟨S_Z1, by simp [generators, ZGenerators], ?_⟩
  exact weightOneAt_anticomm_S_Z1 i _
    (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
```

The `by rcases hi with rfl | rfl <;> tauto` snippet turns the 2-disjunction
`(i = 0 ∨ i = 1)` from `hi_trichotomy` into the 4-disjunction
`(i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)` that the helper needs.

This generalizes cleanly: for an overlapping-Z-stab CSS code with N
disjoint "spine" qubit regions, use an N-way `hi_*tomy` and the same
`by rcases ... <;> tauto` lift to the broader per-helper disjunction.

### 2. `pauli_comm_componentwise` handles disjoint-support mixed-type cases

The plan.md flagged a concern that `pauli_comm_componentwise` might fail
on weight-3 mixed X/Z operators. **It works**: T18 (`X̄_1 = IIXXII` with
support {2,3} vs `Z̄_2 = IIIIZZ` with support {4,5}, disjoint), T21b
(disjoint), T24c (disjoint) all close in one line. The tactic does
not require same-type operands — it just needs every per-qubit pair
to commute, which holds whenever the supports are disjoint (one factor
is I at each qubit position).

This matches the CSS_4_1_2 pattern (logicalX_commutes_S_Z2 — disjoint
{0,1} vs {2,3}). No fallback to explicit Finset needed.

### 3. The k=2 `fin_cases ℓ <;> fin_cases ℓ'` cross-commute dispatch (FourQubit_4_2_2 → C_6)

The `logical_commute_cross` field of `StabilizerCode n 2` has shape

```
(ℓ : Fin 2) → (ℓ' : Fin 2) → ℓ ≠ ℓ' → <quadruple of equations>
```

The four cases unfold cleanly via `fin_cases ℓ <;> fin_cases ℓ'`:
- (0,0) and (1,1): `exact (hne rfl).elim`
- (0,1): `refine ⟨T17, T18, T19.symm, T20⟩`
- (1,0): `refine ⟨T17.symm, T19, T18.symm, T20.symm⟩`

The `.symm` arrangement in (1,0) is what's tricky — copy the
`FourQubit_4_2_2.stabilizerCode` recipe verbatim. The quadruple
`⟨X*X comm, X*Z comm, Z*X comm, Z*Z comm⟩` shape comes from the
`LogicalQubitOps.cross_commute_pair` field shape; if a future
refactor introduces a smart constructor for this, both
`FourQubit_4_2_2` and `SixQubit_6_2_2` can adopt it together.

### 4. T31 helpers with **multiple** `rcases hi` disjunctions

CSS_4_1_2's T31 helpers use a 2-disjunction `i = 0 ∨ i = 1`. C_6
extends to a 4-disjunction `i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3`. The
proof shape extends linearly:

```lean
ext j
rcases hi with rfl | rfl | rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
  simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, ...]
```

For the Z-anticommute helpers (T31c, T31d), no `hP` rcases needed
since `P = Z` is hard-coded.

The 4-disjunction × 2-Pauli × 6-qubit cases (48 per helper) all close
under one `simp` in milliseconds. No performance issue.

## Suggested follow-ups

1. **Lift `pauli_comm_even_anticommutes` + Finset.ext + `decide` boilerplate
   into a tactic.** Every `logicalX_ℓ * S_Zk = S_Zk * logicalX_ℓ` and
   `logicalZ_ℓ * S_Xk = S_Xk * logicalZ_ℓ` lemma in this file (eight of
   them) follows the same 11-line template:

   ```lean
   private lemma logical*_commutes_S_** : ... := by
     classical
     pauli_comm_even_anticommutes
     have hfilter :
         (Finset.univ.filter
               (NQubitPauliGroupElement.anticommutesAt (n := 6)
                 logical*.operators S_**.operators)) =
           ({...} : Finset (Fin 6)) := by
       ext i; fin_cases i <;>
         simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
           logical*, S_**, NQubitPauliOperator.set,
           NQubitPauliOperator.identity, PauliOperator.mulOp]
     rw [hfilter]; decide
   ```

   A `pauli_comm_via_even_filter [g, h] {i1, i2, ...}` notation would
   collapse this to one line per lemma. Same opportunity for
   `pauli_anticomm_via_odd_filter`. CSS_4_1_2, FourQubit_4_2_2, and
   C_6 all repeat this template heavily.

2. **Promote the 3-way trichotomy + 4-disjunction-lift trick to
   `docs/lean-patterns.md`.** The current `hi_dichotomy` documentation
   addresses only the disjoint-support case; the overlap case (this
   code, GOY r ≥ 1, larger Knill codes) is the first instance and
   worth a paragraph in the patterns doc.

3. **`stabilizerCodeWithDistance` is a 4-line repeat across all small
   codes.** A smart constructor `mkStabilizerCodeWithDistance` taking
   the underlying `StabilizerCode` + the distance proof would shave
   ~3 LoC per code and make the boundary between "code defined" and
   "distance proven" cleaner.

4. **`pauli_comm_componentwise` documentation update.** The plan.md
   flagged worry about weight-3 mixed-type cases; our experience
   confirms it works perfectly for disjoint-support cases regardless
   of operator types. Worth noting in `docs/lean-patterns.md` § on
   commutation tactics that the tactic is more flexible than its name
   suggests.

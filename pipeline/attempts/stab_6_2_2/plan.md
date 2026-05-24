# Formalization plan: [[6,2,2]] C_6 code

## Strategy summary

The Knill C_6 [[6,2,2]] code is the **second k = 2 CSS code** to be
formalized in the repo (after `FourQubit_4_2_2.lean`). It is also a
**multi-Z-stabilizer / multi-X-stabilizer** CSS code (like
`CSS_4_1_2.lean`), so the relevant template-blending is:

- **From `FourQubit_4_2_2.lean`** (k = 2 CSS structure): all the logical-
  operator infrastructure (`logicalX_1`, `logicalX_2`, `logicalZ_1`,
  `logicalZ_2`), the pairwise off-diagonal commutation theorems
  (T17–T20), and the `logical_commute_cross` field's `fin_cases ℓ <;>
  fin_cases ℓ'` 4-case dispatch.
- **From `CSS_4_1_2.lean`** (multi-Z-stab CSS structure): the
  `hi_dichotomy` pattern for the weight-1 anticommute witness, plus the
  partial-support Z-generators that don't include `NQubitPauliOperator.identity`
  fall-through in their simp sets.

The distance proof reuses `hasCodeDistance_two_of_anticommute_witness`
(`Framework/Core/CSS/CSSDistance.lean`, introduced in PR #34) — the
proven, reusable distance-2 closer that abstracts the "witness function +
explicit weight-2 logical" boilerplate.

**Distance method**: finite enumeration via the CSS helper. No
homological framework needed; n = 6 is small enough that explicit
witness Finsets are tractable.

**Key structural difference from `FourQubit_4_2_2.lean`**: in
`FourQubit_4_2_2.lean`, the single Z-stab `ZZZZ` covers all 4 qubits, so
the weight-1 anti-witness function trivially picks `Z1` for X/Y errors at
*any* qubit. In C_6, each Z-stab covers only 4 of 6 qubits, so the
weight-1 anti-witness needs a qubit-dependent dispatch (see T31 below).

## Theorem dependency graph

```
T1 (Z-gens Z-type)        T2 (X-gens X-type)
   \                       /
T3,T4,T5,T6 (4 ZX cross-commutes) ←──┐
   \                              T7 (combined ZGenerators_commute_XGenerators)
   |                                  /
T8 (gen pairwise commute) ←───── T1, T2, T7
   |
T9 (-I ∉ subgroup) ←────────────  T1, T2, T7

T10 (list ↔ set)
T11 (phase 0)         T12 (rows indep)
                            \
                             T13 (gens indep)
   \    \    /
T14 (stabilizerGroup.toSubgroup = subgroup) ←─ T10

T15 (X̄_1 ⊥ Z̄_1)         T16 (X̄_2 ⊥ Z̄_2)
T17 (X̄_1 comm X̄_2)       T18 (X̄_1 comm Z̄_2)
T19 (X̄_2 comm Z̄_1)       T20 (Z̄_1 comm Z̄_2)

T21 (X̄_1 ⊥ stabs)  T22 (X̄_2 ⊥ stabs)
T23 (Z̄_1 ⊥ stabs)  T24 (Z̄_2 ⊥ stabs)
       \         |        |        /
T25 (X̄_1 ∈ centralizer)
T26 (X̄_2 ∈ centralizer)
T27 (Z̄_1 ∈ centralizer)
T28 (Z̄_2 ∈ centralizer)
       \   \   /    /
T29 (StabilizerCode 6 2) ← needs T8, T9, T10, T11, T13, T15, T16, T25–T28
                          and T17–T20 for the cross-commute field
       |
T30 (stabilizerCode-side subgroup bridge)
       |
T31 (weight-1 anticomm witness)
       \                              /
        T32 (HasCodeDistance 2) ←── needs T29, T30, T31, T15 (or T16) for the logical witness
              |
        T33 (StabilizerCodeWithDistance 6 2 2)
```

## Per-theorem proof sketch

### T1: ZGenerators are Z-type
- **Approach**: `rcases hg with rfl | rfl`; per generator, `fin_cases i
  <;> simp [PauliOperator.IsZType, S_Z*, NQubitPauliOperator.set,
  NQubitPauliOperator.identity]`.
- **Reuse**: line-for-line analog of `CSS_4_1_2.ZGenerators_are_ZType`
  (2 generators).
- **Note**: BOTH `S_Z1` and `S_Z2` have partial support (cover only 4 of
  6 qubits). Keep `NQubitPauliOperator.identity` in the simp set for the
  qubits where the stabilizer's `.set` chain doesn't reach.
- **Difficulty**: trivial.

### T2: XGenerators are X-type
- **Approach**: same as T1, with `S_X1`, `S_X2`.
- **Difficulty**: trivial.

### T3: `S_Z1 * S_X1 = S_X1 * S_Z1` (`ZZZZ II` vs `XXXX II`)
- **Approach**: `pauli_comm_even_anticommutes`; anticomm-filter Finset
  is `{0, 1, 2, 3}` (size 4 = even).
- **Reuse**: direct analog of `FourQubit_4_2_2.Z1_comm_X1` (which uses
  Finset `{0,1,2,3}` over `Fin 4`); here it's `{0,1,2,3}` over `Fin 6`.
- **Difficulty**: trivial.

### T4: `S_Z1 * S_X2 = S_X2 * S_Z1` (`ZZZZ II` vs `XX II XX`)
- **Approach**: `pauli_comm_even_anticommutes`; anticomm-filter Finset
  is `{0, 1}` (size 2 = even).
- **Reuse**: analog of `CSS_4_1_2.S_Z1_comm_S_X1` (filter `{0,1}` over
  `Fin 4`).
- **Difficulty**: trivial.

### T5: `S_Z2 * S_X1 = S_X1 * S_Z2` (`ZZ II ZZ` vs `XXXX II`)
- **Approach**: `pauli_comm_even_anticommutes`; anticomm-filter Finset
  is `{0, 1}` (size 2 = even).
- **Difficulty**: trivial.

### T6: `S_Z2 * S_X2 = S_X2 * S_Z2` (`ZZ II ZZ` vs `XX II XX`)
- **Approach**: `pauli_comm_even_anticommutes`; anticomm-filter Finset
  is `{0, 1, 4, 5}` (size 4 = even).
- **Difficulty**: trivial.

### T7: `ZGenerators_commute_XGenerators`
- **Approach**: `rcases hz with rfl | rfl; rcases hx with rfl | rfl`;
  exact T3/T4/T5/T6 in each branch.
- **Reuse**: line-for-line analog of `CSS_4_1_2.ZGenerators_commute_XGenerators`
  (2 Z gens × 1 X gen), extended to 2 × 2 = 4 cases.
- **Difficulty**: trivial.

### T8: all-pair generator commutation
- **Approach**: standard CSS structural argument; reuse
  `CSSCommutationLemmas.ZType_commutes` and `XType_commutes`.
  Case-split on `(g, h) ∈ (Z ∪ X) × (Z ∪ X)`.
- **Reuse**: copy `FourQubit_4_2_2.generators_commute` verbatim.
- **Difficulty**: trivial.

### T9: `−I ∉ subgroup`
- **Approach**: one-shot via `CSS.negIdentity_not_mem_closure_union`,
  fed T1, T2, and the cross-commutation T7.
- **Reuse**: copy `FourQubit_4_2_2.negIdentity_not_mem` verbatim.
- **Difficulty**: trivial.

### T10: `listToSet generatorsList = generators`
- **Approach**: `ext g; simp` after unfolding. Four elements in the
  list, four in the set.
- **Reuse**: minor adaptation of `CSS_4_1_2.listToSet_generatorsList`
  (which has 3 elements, here we extend to 4).
- **Difficulty**: trivial.

### T11: `AllPhaseZero generatorsList`
- **Approach**: chain of `AllPhaseZero_cons.mpr ⟨rfl, …⟩` per element.
  Four elements ⇒ four nested `⟨rfl, …⟩`.
- **Reuse**: pattern from `CSS_4_1_2.AllPhaseZero_generatorsList`.
- **Difficulty**: trivial.

### T12: rows linearly independent
- **Approach**: `by decide`. Four rows in `(GF(2))^12`; concrete and tractable.
- **Difficulty**: trivial.

### T13: generators independent
- **Approach**: one-line consequence of T12 via
  `GeneratorsIndependent_of_rowsLinearIndependent`.
- **Difficulty**: trivial.

### T14: `stabilizerGroup.toSubgroup = subgroup`
- **Approach**: unfold `mkStabilizerFromGenerators` + apply T10.
- **Reuse**: copy `CSS_4_1_2.stabilizerGroup_toSubgroup_eq` verbatim.
- **Difficulty**: trivial.

### T15: `Anticommute logicalX_1 logicalZ_1` (`IIXXII` vs `ZIIZZI`)
- **Approach**: `pauli_anticomm_odd_anticommutes`; anticomm-filter
  Finset is `{3}` (size 1 = odd). At qubit 3: X·Z (anticomm). At
  qubits 0 (I·Z), 2 (X·I), 4 (I·Z): commute.
- **Reuse**: analog of `FourQubit_4_2_2.logicalX_1_anticommutes_logicalZ_1`.
- **Difficulty**: trivial.

### T16: `Anticommute logicalX_2 logicalZ_2` (`IXIXXI` vs `IIIIZZ`)
- **Approach**: `pauli_anticomm_odd_anticommutes`; anticomm-filter
  Finset is `{4}` (size 1 = odd). At qubit 4: X·Z (anticomm). Other
  positions trivially commute.
- **Difficulty**: trivial.

### T17: `logicalX_1 * logicalX_2 = logicalX_2 * logicalX_1`
- **Approach**: both X-type ⇒ trivially commute via
  `pauli_comm_componentwise [logicalX_1, logicalX_2]`.
- **Reuse**: copy `FourQubit_4_2_2.logicalX_1_commutes_logicalX_2`.
- **Difficulty**: trivial.

### T18: `logicalX_1 * logicalZ_2 = logicalZ_2 * logicalX_1` (`IIXXII` vs `IIIIZZ`)
- **Approach**: supports disjoint ({2,3} vs {4,5}) ⇒ empty filter ⇒
  even count 0. Could use `pauli_comm_componentwise` (since they have
  no overlap, the I·X and X·I per-qubit factors trivially commute) OR
  the explicit empty-Finset filter.
- **Decision**: use `pauli_comm_componentwise` (cleaner — no `decide`
  on the cardinality).
- **Difficulty**: trivial.

### T19: `logicalX_2 * logicalZ_1 = logicalZ_1 * logicalX_2` (`IXIXXI` vs `ZIIZZI`)
- **Approach**: overlap = {3, 4}; anticomm-filter Finset is `{3, 4}`
  (size 2 = even). Use `pauli_comm_even_anticommutes` with explicit
  filter.
- **Reuse**: analog of `FourQubit_4_2_2.logicalX_1_commutes_logicalZ_2`.
- **Difficulty**: trivial.

### T20: `logicalZ_1 * logicalZ_2 = logicalZ_2 * logicalZ_1`
- **Approach**: both Z-type ⇒ trivially commute via
  `pauli_comm_componentwise`.
- **Reuse**: copy `FourQubit_4_2_2.logicalZ_1_commutes_logicalZ_2`.
- **Difficulty**: trivial.

### T21–T24: each logical commutes with each generator (4 logicals × 4 gens = 16 lemmas)

Detailed cases (size of anticomm-filter Finset for the `pauli_comm_even_anticommutes` cases):

| Logical | vs `S_Z1` | vs `S_Z2` | vs `S_X1` | vs `S_X2` |
|---------|-----------|-----------|-----------|-----------|
| `X_L=IIXXII` (T21) | `{2,3}` (2) | `∅` (0) | both X | both X |
| `X_S=IXIXXI` (T22) | `{1,3}` (2) | `{1,4}` (2) | both X | both X |
| `Z_L=ZIIZZI` (T23) | both Z | both Z | `{0,3}` (2) | `{0,4}` (2) |
| `Z_S=IIIIZZ` (T24) | both Z | both Z | `∅` (0) | `{4,5}` (2) |

Use `pauli_comm_componentwise` for both-X-type/both-Z-type and for empty-overlap
cases; use `pauli_comm_even_anticommutes` + explicit filter for the rest.

- **Reuse**: 8 lemmas use direct analogs of patterns in
  `FourQubit_4_2_2.lean` / `CSS_4_1_2.lean`; 8 lemmas use trivial
  componentwise dispatch.
- **Difficulty**: standard mechanical.

### T25: `logicalX_1 ∈ centralizer stabilizerGroup`
- **Approach**: `rw [StabilizerGroup.mem_centralizer_iff,
  stabilizerGroup_toSubgroup_eq, subgroup]; rw [Subgroup.forall_comm_closure_iff];
  intro s hs;` then case-split on the union and unfold.
- **Reuse**: copy `FourQubit_4_2_2.logicalX_1_mem_centralizer` (4-way
  case split since we have 2-Z + 2-X here, not 1-Z + 1-X).
- **Difficulty**: trivial.

### T26, T27, T28: same template as T25 for `X_2, Z_1, Z_2`.

### T29: `StabilizerCode 6 2` packaging
- **Approach**: structure literal. The key complication vs.
  `CSS_4_1_2.stabilizerCode` (k = 1) is the `logical_commute_cross`
  field. For k = 2 it cannot use `Subsingleton.elim`; instead use
  `fin_cases ℓ <;> fin_cases ℓ'` (the 4-case dispatch from
  `FourQubit_4_2_2.stabilizerCode`):
  ```
  logical_commute_cross := by
    intro ℓ ℓ' hne
    fin_cases ℓ <;> fin_cases ℓ'
    · exact (hne rfl).elim    -- (0, 0)
    · refine ⟨T17, T18, T19.symm, T20⟩    -- (0, 1)
    · refine ⟨T17.symm, T19, T18.symm, T20.symm⟩    -- (1, 0)
    · exact (hne rfl).elim    -- (1, 1)
  ```
- **Reuse**: copy `FourQubit_4_2_2.stabilizerCode` shape (k = 2 case).
- **Difficulty**: standard.

### T30: stabilizer-code subgroup bridge
- **Approach**: `change` + `rw [listToSet_generatorsList]`.
- **Reuse**: copy `CSS_4_1_2.stabilizerCode_toSubgroup_eq`.
- **Difficulty**: trivial.

### T31: weight-1 anticommute witness
**This is the most novel theorem in the file.** Strategy:

```
∀ i : Fin 6, ∀ P : PauliOperator, P ≠ I →
  ∃ g ∈ generators, Anticommute (weightOneAt i P) g
```

**Approach.** Three-way `hi_trichotomy` on qubit `i`:
```
have hi_trichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5) := by
  fin_cases i <;> tauto
```

Then dispatch on `P`:
- `P = X` or `P = Y`: pick Z-stab.
  - `(i = 0 ∨ i = 1)`: either `S_Z1` or `S_Z2` works; pick `S_Z1` for canonicality.
  - `(i = 2 ∨ i = 3)`: only `S_Z1` covers, use it.
  - `(i = 4 ∨ i = 5)`: only `S_Z2` covers, use it.
- `P = Z`: pick X-stab — dual analysis (same partition).
  - `(i = 0 ∨ i = 1)`: pick `S_X1`.
  - `(i = 2 ∨ i = 3)`: only `S_X1` covers.
  - `(i = 4 ∨ i = 5)`: only `S_X2` covers.

**Three helper lemmas** (mirroring `CSS_4_1_2.lean`'s 3 helpers):

```
-- For (i ∈ {0,1,2,3}, P ∈ {X,Y}): weight-1 at i anticommutes with S_Z1.
weightOneAt_anticomm_S_Z1 (i : Fin 6) (P : PauliOperator)
  (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
  (hP : P = X ∨ P = Y) : Anticommute (weightOneAt i P) S_Z1

-- For (i ∈ {0,1,4,5}, P ∈ {X,Y}): weight-1 at i anticommutes with S_Z2.
weightOneAt_anticomm_S_Z2 (i : Fin 6) (P : PauliOperator)
  (hi : i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5)
  (hP : P = X ∨ P = Y) : Anticommute (weightOneAt i P) S_Z2

-- For (i ∈ {0,1,2,3}, P = Z): weight-1 Z at i anticommutes with S_X1.
weightOneAt_Z_anticomm_S_X1 (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
  : Anticommute (weightOneAt i Z) S_X1
```

Plus one more for `S_X2` (qubits {0,1,4,5}, P = Z).

The proof shape for each helper is line-by-line analogous to
`CSS_4_1_2.weightOneAt_anticomm_S_Z1`, just with `Fin 6` instead of
`Fin 4` and a 4-way `rcases hi` instead of 2-way.

- **Difficulty**: **standard**; this is the longest single proof in the
  file. ~30 LoC.

### T32: `HasCodeDistance stabilizerCode 2`
- **Approach**: one-line via `hasCodeDistance_two_of_anticommute_witness`.
- **Reuse**: copy `CSS_4_1_2.code_has_distance_two` line 487, switching
  in T31 as the witness and `logicalX_1` (or `logicalZ_2`) as the
  weight-2 nontrivial logical.
- **Difficulty**: trivial.

### T33: `StabilizerCodeWithDistance 6 2 2`
- **Approach**: one-line structure literal bundling T29 + T32.
- **Difficulty**: trivial.

## Risk register

1. **Three-way partition vs. two-way `hi_dichotomy`.** `CSS_4_1_2.lean`
   used a clean 2-way dichotomy (qubits {0,1} vs {2,3}). C_6 has a
   three-way partition ({0,1} | {2,3} | {4,5}), but the {0,1} subset is
   ambiguous (covered by both Z-stabs). The plan resolves the ambiguity
   by picking `S_Z1` for {0,1}, and the helper lemmas are scoped to the
   correct subset. **Mitigation**: factor the four-disjunction
   hypotheses (e.g. `i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3` for `S_Z1`) into
   the helpers' preconditions to keep the dispatch readable.

2. **Larger `fin_cases i <;> fin_cases j` in helper lemmas.** For
   `Fin 6 × Fin 6` in the `ext j` step of each helper, the inner
   `fin_cases j` runs over 6 values, the outer over 4 (for the
   per-stab support). 24 cases per `rcases hP` branch × 2 P-branches =
   48 cases. Should still close in seconds with `simp [...]`. **Risk**:
   if `simp` is slow, fall back to `omega` or `decide` after `ext`. No
   real risk; `FiveQubit_5_1_3.lean` deals with similar combinatorics
   for n = 5.

3. **`pauli_comm_componentwise` performance with mixed weight-3 + weight-3
   logicals.** `X_S = IXIXXI` and `Z_L = ZIIZZI` both have weight 3 (not
   weight 2 like `[[4,2,2]]`'s logicals). The component-wise check at all
   6 qubits with mixed I/X/Z entries should still close fast, but watch
   for `lake build` timeouts if `simp` chains explode. **Mitigation**: use
   `pauli_comm_even_anticommutes` + explicit `{i, j}` filter as a fallback.

4. **EC Zoo vs. Knill paper for logical operators.** The EC Zoo entry
   *cites* Knill 2004 for the logical operators, but the exact form
   `X_L=IIXXII, Z_L=ZIIZZI, X_S=IXIXXI, Z_S=IIIIZZ` is from the EC Zoo
   entry, not the paper text itself. We verified all 16 stabilizer-vs-
   logical commutations + 6 pairwise logical commutations in
   `informal_spec.md`. **If a reviewer disputes**, the verification
   table is right there and reproducible. **Mitigation in place.**

5. **`linter.unusedSimpArgs` from `NQubitPauliOperator.identity` in
   X-generator simp sets.** Per `docs/lean-patterns.md` § "`identity` in
   simp sets for CSS generator equality", X-generators of C_6 cover
   only 4 of 6 qubits, so `identity` IS needed in the simp set (qubits
   {4,5} for `S_X1`, qubits {2,3} for `S_X2` fall through to identity).
   **Action**: keep `NQubitPauliOperator.identity` in the simp set for
   T1 *and* T2 (in C_6 the X-side is partial-support unlike the
   [[4,2,2]] case).

6. **`logical_commute_cross` quadruple ordering.** Each off-diagonal
   case requires four equations in a specific order:
   ```
   X_ℓ * X_ℓ' = X_ℓ' * X_ℓ ∧
   X_ℓ * Z_ℓ' = Z_ℓ' * X_ℓ ∧
   Z_ℓ * X_ℓ' = X_ℓ' * Z_ℓ ∧
   Z_ℓ * Z_ℓ' = Z_ℓ' * Z_ℓ
   ```
   For `(ℓ, ℓ') = (0, 1)`: takes T17, T18, T19.symm, T20.
   For `(ℓ, ℓ') = (1, 0)`: takes T17.symm, T19, T18.symm, T20.symm.
   **Mitigation**: copy `FourQubit_4_2_2.lean:457-467` verbatim — it
   already has the right symmetry pattern worked out for k = 2.

## Estimated effort

- **Lines of code**: ~500 (catalog estimate was 300; the multi-Z-stab +
  multi-X-stab combinatorics push the helper count to ~16 logicals×stab
  commutation lemmas + 4 helper lemmas for T31, so 500 is more realistic.
  CSS_4_1_2 ended up at 505 LoC with 3 generators × 1 logical-X +
  1 logical-Z, so C_6 with 4 generators × 2 logical-X + 2 logical-Z
  scales linearly to ~550 LoC, but some lemmas are shared between
  logicals so 500 is a reasonable midpoint).
- **Hours**: ~3 for an experienced agent following the
  `FourQubit_4_2_2.lean` + `CSS_4_1_2.lean` blended template. No novel
  proof patterns required.
- **Longest theorem**: T31 (weight-1 anticommute witness, ~30 LoC with
  helpers). Should close in one attempt if helpers are written correctly.
- **Total sorry count to close**: 33 (one per theorem).

## Why this is well-suited to engineering track

- **No new framework needed.** All required infrastructure is in place:
  `hasCodeDistance_two_of_anticommute_witness` (PR #34), CSS predicates,
  `IsXTypeElement`, `IsZTypeElement`, the cross-commutation lemmas, the
  `LogicalQubitOps` k = 2 packaging.
- **Two strong templates.** `FourQubit_4_2_2.lean` (k = 2 structure) +
  `CSS_4_1_2.lean` (multi-Z-stab structure). Blend the two.
- **Small n.** All `decide` / `fin_cases` proofs close in seconds.
- **Concrete, well-cited code.** Knill 2004 is heavily cited and
  the EC Zoo entry is precise. No spec ambiguity.
- **Useful regression test.** First k = 2 multi-Z-stab CSS code; if
  the proof pattern works here, it generalizes cleanly to GOY
  (parametric) and other [[k+4, k, 2]] H-code instances.

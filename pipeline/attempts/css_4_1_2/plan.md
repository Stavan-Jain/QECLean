# Formalization plan: [[4,1,2]] LNCY code

## Strategy summary

The [[4,1,2]] LNCY code is a CSS code with **2 Z-stabilizers + 1 X-stabilizer**
on 4 qubits, encoding 1 logical qubit. The structure is exceptionally close
to the existing `FourQubit_4_2_2.lean` (same n = 4, same CSS detection
shape), differing only in:

- **Stabilizer split**: LNCY has `(ZZII, IIZZ, XXXX)` (2 Z + 1 X) vs.
  `[[4,2,2]]`'s `(ZZZZ, XXXX)` (1 Z + 1 X);
- **Logical structure**: k = 1 instead of k = 2, so the
  `Subsingleton.elim`-shortcut closes `logical_commute_cross` (no need for
  the off-diagonal pairwise commutation theorems);
- **Logical operators**: `logicalX = XXII`, `logicalZ = ZIZI` (specific
  Paulis on weight-2 supports) instead of the four logicals
  `IXIX/IIXX/IIZZ/IZIZ` of the [[4,2,2]] code.

The distance proof reuses the existing
`no_weight_one_mem_centralizer_of_anticommute_witness` helper
(`Framework/Core/CSS/CSSDistance.lean`) — essentially the same proof
shape as `FourQubit_4_2_2.lean`'s `code_has_distance_two`, adjusted for
the new generator partition.

**Distance method**: finite enumeration via the standard CSS helper. No
homological framework needed; n = 4 is small enough that `decide` on
weight-1 anti-witness suffices.

## Theorem dependency graph

```
T1 (Z-type)       T3 (S_Z1·S_X1 = comm)     T8 (phase 0)
T2 (X-type)       T4 (S_Z2·S_X1 = comm)     T9 (rows indep)
   \                 /
    T5 (gen commute)        T7 (list ↔ set)        T10 (gens indep, ← T9)
       \                       /
        T6 (-I ∉ subgroup)     T11 (stabGroup.toSubgroup = subgroup)
              \                  /
               T8 + T10 + T6 → T17 partial setup
                          |
T12 (X̄ ⊥ Z̄)              |
T13 (X̄ ⊥ stabs)  T14 (Z̄ ⊥ stabs)
       \              /
        T15, T16 (logicals in centralizer)
              \    /
              T17 (StabilizerCode 4 1) ← needs T7, T8, T10, T5, T6, T12, T15, T16
                 |
              T18 (subgroup bridge)
                 |
T19 (weight-1 anticomm witness)
                 |
              T20 (HasCodeDistance 2) ← needs T17, T18, T19, T12 (logicalX nontrivial)
                 |
              T21 (StabilizerCodeWithDistance)
```

## Per-theorem proof sketch

### T1: ZGenerators are Z-type
- Approach: `rcases hg with rfl | rfl`; then for each generator, `fin_cases i <;> simp [...]` on the per-qubit predicate.
- Reuse: copy `FourQubit_4_2_2.ZGenerators_are_ZType` verbatim, expand to 2 generators instead of 1.
- Difficulty: **trivial**.

### T2: XGenerators are X-type
- Approach: same as T1, with only 1 X-generator (matching `FourQubit_4_2_2.XGenerators_are_XType`).
- Difficulty: **trivial**.

### T3: `S_Z1 * S_X1 = S_X1 * S_Z1` (i.e. `ZZII` and `XXXX`)
- Approach: `pauli_comm_even_anticommutes`; the anticommute-filter Finset is `{0, 1}` (size 2 = even).
- Reuse: line-for-line analog of `Z1_comm_X1` in `FourQubit_4_2_2.lean:114`.
- Difficulty: **trivial** (standard CSS pattern).

### T4: `S_Z2 * S_X1 = S_X1 * S_Z2` (i.e. `IIZZ` and `XXXX`)
- Approach: same; anticommute-filter Finset is `{2, 3}` (size 2 = even).
- Difficulty: **trivial**.

### T5: all-pair generator commutation
- Approach: standard CSS structural argument; reuse
  `CSSCommutationLemmas.ZType_commutes` and `XType_commutes`. Case-split
  on `(g, h) ∈ (Z ∪ X) × (Z ∪ X)`.
- Reuse: copy `FourQubit_4_2_2.generators_commute` verbatim.
- Difficulty: **trivial**.

### T6: `-I ∉ subgroup`
- Approach: one-shot via `CSS.negIdentity_not_mem_closure_union`, fed
  T1, T2, and the cross-commutation T3+T4 packaged as
  `ZGenerators_commute_XGenerators`.
- Reuse: copy `FourQubit_4_2_2.negIdentity_not_mem` verbatim.
- Difficulty: **trivial**.

### T7: `listToSet generatorsList = generators`
- Approach: `ext g; simp` after unfolding. Three elements in the list,
  three in the set (split as 2-Z + 1-X union).
- Reuse: minor adaptation of `FourQubit_4_2_2.listToSet_generatorsList`.
- Difficulty: **trivial**.

### T8: `AllPhaseZero generatorsList`
- Approach: chain of `AllPhaseZero_cons.mpr ⟨rfl, …⟩` per element.
  Three elements ⇒ three nested `⟨rfl, …⟩`.
- Reuse: pattern from any small code (Steane7 has 6, [[4,2,2]] has 2).
- Difficulty: **trivial**.

### T9: rows linearly independent
- Approach: `by decide`. Three rows in `(GF(2))^8`; concrete and tiny.
- Difficulty: **trivial**.

### T10: generators independent
- Approach: one-line consequence of T9 via
  `GeneratorsIndependent_of_rowsLinearIndependent`.
- Difficulty: **trivial**.

### T11: `stabilizerGroup.toSubgroup = subgroup`
- Approach: unfold `mkStabilizerFromGenerators` + apply T7.
- Reuse: copy `FourQubit_4_2_2.stabilizerGroup_toSubgroup_eq` verbatim.
- Difficulty: **trivial**.

### T12: `Anticommute logicalX logicalZ` (i.e. `XXII` vs `ZIZI`)
- Approach: `pauli_anticomm_odd_anticommutes`; anticommute-filter Finset
  is `{0}` (size 1 = odd). Q1 (X·I), Q2 (I·Z), Q3 (I·I) all commute.
- Reuse: pattern from `FourQubit_4_2_2.logicalX_1_anticommutes_logicalZ_1`.
- Difficulty: **trivial**.

### T13: `logicalX` commutes with each generator (3 lemmas)
- Approach: per generator, `pauli_comm_even_anticommutes` + explicit
  Finset. Cases:
  - vs `S_Z1=ZZII`: filter `{0, 1}` (size 2).
  - vs `S_Z2=IIZZ`: filter `{}` (size 0).
  - vs `S_X1=XXXX`: `pauli_comm_componentwise` (both X-type).
- Reuse: combinations of `FourQubit_4_2_2.logicalX_i_commutes_*` patterns.
- Difficulty: **trivial**.

### T14: `logicalZ` commutes with each generator (3 lemmas)
- Approach: dual of T13. Cases:
  - vs `S_Z1=ZZII`: `pauli_comm_componentwise` (both Z-type).
  - vs `S_Z2=IIZZ`: `pauli_comm_componentwise` (both Z-type).
  - vs `S_X1=XXXX`: filter `{0, 2}` (size 2).
- Difficulty: **trivial**.

### T15: `logicalX ∈ centralizer stabilizerGroup`
- Approach: standard idiom (used in `FourQubit_4_2_2.lean`):
  ```
  rw [StabilizerGroup.mem_centralizer_iff,
      stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  ...
  ```
- Reuse: copy `FourQubit_4_2_2.logicalX_1_mem_centralizer` verbatim
  (modulo generator-set unfolding).
- Difficulty: **trivial**.

### T16: `logicalZ ∈ centralizer stabilizerGroup`
- Approach: same as T15.
- Difficulty: **trivial**.

### T17: `StabilizerCode 4 1` packaging
- Approach: structure literal with fields populated from T7–T16.
  `logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim`
  closes the cross-commute field trivially in the `k = 1` case.
- Reuse: copy `Steane7.stabilizerCode` shape (`k = 1` case).
- Difficulty: **trivial**.

### T18: `stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators`
- Approach: unfold + apply T7.
- Reuse: pattern from `FourQubit_4_2_2.stabilizerCode_toSubgroup_eq`
  (it's `private` there; we'll need to re-prove or mirror it).
- Difficulty: **trivial**.

### T19: weight-1 anticommute witness
- Approach: backtracking dispatch by `(i, P)` cases:
  ```
  match P, hP with
  | .X, _ | .Y, _ => ⟨S_Z_(i covers), ..., weight_anticomm_Z_proof⟩
  | .Z, _ => ⟨S_X1, ..., weight_anticomm_X1_proof⟩
  | .I, hP => exact (hP rfl).elim
  ```
  Two helper lemmas needed:
  - `weightOneAt_anticomm_S_Z (i : Fin 4) (P ∈ {X, Y})`: for the Z-side,
    pick `S_Z1` if `i ∈ {0,1}`, `S_Z2` if `i ∈ {2,3}`. Internally
    `fin_cases i` splits.
  - `weightOneAt_Z_anticomm_S_X1 (i : Fin 4)`: weight-1 Z at any qubit
    anticommutes with `S_X1 = XXXX`.
- Reuse: very close to `FourQubit_4_2_2.weight_one_anticomm_witness`,
  with the twist that we need to pick which Z-generator to use (the
  [[4,2,2]] code had only one Z, so no branching). Use a sub-case on
  `i < 2` vs `i ≥ 2`.
- Difficulty: **standard** (slightly more cases than [[4,2,2]]).

### T20: `HasCodeDistance stabilizerCode 2`
- Approach:
  ```
  refine hasCodeDistance_of stabilizerCode 2 (by decide)
    ⟨logicalX, (logicalOps 0).xOp_nontrivial, by decide⟩ ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  interval_cases w
  -- w = 1 case: use T19 + helper
  rcases (IsNontrivialLogicalOperator_iff _ _).mp h_nontrivial with ⟨h_cent, _, _⟩
  exact no_weight_one_mem_centralizer_of_anticommute_witness
    stabilizerCode.toStabilizerGroup generators T18 T19 g hg_weight h_cent
  ```
- Reuse: copy `FourQubit_4_2_2.code_has_distance_two` (line 534).
- Difficulty: **standard**.

### T21: `StabilizerCodeWithDistance 4 1 2`
- Approach: one-line structure literal bundling T17 + T20.
- Difficulty: **trivial**.

## Risk register

1. **Tableau-vs-codewords confusion**. The EC Zoo description quotes a
   Qiskit tableau `(XXII, IIXX, ZZZZ)` that is the *dual* of our chosen
   stabilizer `(ZZII, IIZZ, XXXX)` (X and Z roles flipped, same up to
   CSS swap). If a reviewer interprets the EC Zoo tableau as the
   ground-truth stabilizer, they would mark our `logicalX = XXII` as
   wrong (it would be a stabilizer under their convention) and demand
   `logicalX = ZZZZ` or `ZZII`. We document this clearly in
   `informal_spec.md` § "Stabilizer generators" — the chosen
   stabilizers are dictated by the LNCY paper's *codewords* (Eqs. 5–6),
   not by the Qiskit preset. **Mitigation already in place**.

2. **Logical Z support choice ambiguity**. `logicalZ = ZIZI` is one
   valid choice; `logicalZ' = IZIZ` differs from it by `ZZZZ`, and
   `ZZZZ = S_Z1 · S_Z2` lies in the stabilizer. So `ZIZI` and `IZIZ`
   are the same logical Z modulo the stabilizer. The choice is
   arbitrary; we pick `ZIZI` for symmetry with `logicalX = XXII`. No
   theorem statement depends on this choice except T14 (the support
   of the explicit Finset would change).

3. **`hasCodeDistance_of` step for `w = 0` lower bound**. The helper
   signature in `CodeDistance.lean:52` takes `∀ w, 1 ≤ w → w < d → ...`,
   so `w = 0` is excluded. With `d = 2`, only `w = 1` needs handling,
   making this very clean.

4. **Worktree symlink**. Done at setup — `lake build` should reuse
   main's mathlib. If a future `lake build` fails with "Mathlib not
   found", check `.lake/packages` symlink integrity.

## Estimated effort

- **Lines of code**: ~320 (slightly above the catalog's 300 estimate;
  the extra Z-generator + one extra cross-commutation lemma vs. the
  [[4,2,2]] file account for the bulk).
- **Hours**: ~2–3 for an experienced agent following the
  `FourQubit_4_2_2.lean` template.
- **Longest theorem**: T19 (weight-1 anticommute witness) with ~8
  cases. Should close in one attempt if the helper lemmas are written
  carefully.
- **Total sorry count to close**: 21 (one per theorem; some bundle
  several lemmas into one `sorry` block for atomicity, see the Lean
  skeleton's `TODO(css_4_1_2-T<n>)` markers).

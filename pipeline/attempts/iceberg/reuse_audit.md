# Reuse audit: iceberg `[[2m, 2m−2, 2]]`

## Directly applicable (use as-is)

### Pauli-group foundations

- `NQubitPauliGroupElement n` — `QEC/Stabilizer/Foundations/PauliGroup/NQubitElement.lean`.
- `NQubitPauliOperator n`, `.identity n`, `.X n`, `.Z n`, `.set i P`
  — `QEC/Stabilizer/Foundations/PauliGroup/NQubitOperator.lean`. The "all-X"
  and "all-Z" constructors are direct fits for the iceberg's full-support
  generators.
- `PauliOperator.X`, `.Z`, `.Y`, `.I`, `.IsXType`, `.IsZType`, `.mulOp`
  — `QEC/Stabilizer/Foundations/PauliGroupSingle/Operator.lean`.

### Commutation infrastructure

- **`pauli_comm_even_anticommutes` tactic**
  — `Foundations/PauliGroup/CommutationTactics.lean`. Reduces a commutation
  goal to "`Even ((Finset.univ.filter anticommutesAt).card)`". Used for T3
  (stabilizer commutation), T11–T14 (logical commutations), T17 helpers
  (weight-1 anti-witnesses).
- **`pauli_anticomm_odd_anticommutes` tactic** — same file. Dual of above;
  reduces `Anticommute` to "`Odd (... .card)`". Used for T11 (logical X̄
  anticomm logical Z̄).
- **`pauli_comm_componentwise [...]` tactic** — same file. Closes
  componentwise-commutation when generators have disjoint or matching
  Pauli supports. Useful for the trivial "X̄·X̄" and "Z̄·Z̄" cases of T12,
  and for "logical commutes with same-type stabilizer".
- **`commutes_of_componentwise_commutes`** — `Foundations/PauliGroup/Commutation.lean`.
- **`Anticommute`** predicate — `Foundations/PauliGroup/Commutation.lean:233`.
- **`anticommutesAt`** function — same file.

### CSS predicates and lemmas

- `IsZTypeElement`, `IsXTypeElement`
  — `Framework/Core/CSS/CSSPredicates.lean`. Direct fit for T1, T2.
- `CSSCommutationLemmas.ZType_commutes`, `.XType_commutes`
  — `Framework/Core/CSS/CSSCommutationLemmas.lean`. Used for T4 (all-pair
  commutation) and inside the centralizer proofs for the trivial cases.
- `CSS.negIdentity_not_mem_closure_union`
  — `Framework/Core/CSS/CSSNoNegI.lean`. Direct fit for T5.

### Stabilizer-code structure

- `StabilizerGroup n`, `.toSubgroup`, `.is_abelian`, `.no_neg_identity`
  — `Framework/Core/Stabilizer/StabilizerGroup.lean`.
- `mkStabilizerFromGenerators n L h_comm h_no_neg`
  — `Framework/Core/Stabilizer/StabilizerCode.lean:62`.
- `centralizer S`, `.mem_centralizer_iff`,
  `.mem_centralizer_iff_closure`
  — `Framework/Core/Stabilizer/Centralizer.lean`.
- `Subgroup.forall_comm_closure_iff` — `Framework/Core/Stabilizer/SubgroupLemmas.lean`.
- `negIdentity n`, `.negIdentity_eq_minusOne`, `.negIdentity_ne_one`
  — `Foundations/PauliGroup/NQubitElement.lean`.

### Generator-list / symplectic plumbing

- `NQubitPauliGroupElement.listToSet`, `.listToSet_cons`, `.listToSet_nil`
  — `Foundations/PauliGroup/NQubitElement.lean`.
- `NQubitPauliGroupElement.AllPhaseZero`, `.AllPhaseZero_cons`,
  `.AllPhaseZero_nil` — same file. Used in T7.
- `NQubitPauliGroupElement.rowsLinearIndependent` — same file.
- `GeneratorsIndependent`, `GeneratorsIndependent_of_rowsLinearIndependent`
  — `Framework/Core/Stabilizer/StabilizerCode.lean:42, 48`. Used in T8.

### Logical-operator structure

- `LogicalQubitOps n S` — `Framework/Core/Logical/LogicalOperators.lean:189`.
  The 5-field structure (xOp, zOp, x_mem_centralizer, z_mem_centralizer,
  anticommute) is the target of T15's `logicalOps` field.
- `IsNontrivialLogicalOperator`, `LogicalQubitOps.xOp_nontrivial`,
  `.zOp_nontrivial` — same file.

### Code distance

- **`hasCodeDistance_two_of_anticommute_witness`**
  — `Framework/Core/CSS/CSSDistance.lean:165` (NEW in PR #34). **This is
  the canonical closer for T18.** Saves ~5 LoC of `interval_cases` /
  `rcases` boilerplate that every distance-2 CSS code would otherwise
  reproduce.

  Signature:
  ```
  theorem hasCodeDistance_two_of_anticommute_witness {k : ℕ}
      (C : StabilizerCode n k)
      (genSet : Set (NQubitPauliGroupElement n))
      (h_closure : C.toStabilizerGroup.toSubgroup = Subgroup.closure genSet)
      (h_anticomm : ∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
        ∃ g ∈ genSet, Anticommute (weightOneAt i P) g)
      (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧
        weight g = 2) :
      HasCodeDistance C 2
  ```
- **`no_weight_one_mem_centralizer_of_anticommute_witness`**
  — `Framework/Core/CSS/CSSDistance.lean:32` (transitively used by the
  above; we do not call it directly).
- `weightOneAt i P` — `Framework/Core/CSS/CSSDistance.lean:26`. The
  parametric weight-1 element constructor used in T17.
- `HasCodeDistance`, `hasCodeDistance_of`
  — `Framework/Core/Logical/CodeDistance.lean`.
- `StabilizerCodeWithDistance n k d`
  — `Framework/Core/Logical/CodeDistance.lean:81`. Final packaging in T19.

## Lightly adapted (existing pattern, new instance)

### Generator structure (from `FourQubit_4_2_2.lean`)

- The `[S_Z, S_X]` two-generator pattern (one Z, one X, both full-support):
  copy from `FourQubit_4_2_2.lean:174` (`generatorsList := [Z1, X1]`).
  Generalize the explicit `4` to `2 * m` and the explicit `.set 0`/`1`/`2`/`3`
  chains to `NQubitPauliOperator.Z (2 * m)` / `NQubitPauliOperator.X (2 * m)`.

### Z-type / X-type predicate proofs (from `FourQubit_4_2_2.lean`)

- `ZGenerators_are_ZType` pattern (`FourQubit_4_2_2.lean:88–96`): replace
  the singleton `rcases hg with rfl` and `fin_cases i` with a parametric
  `intro i` and direct `PauliOperator.IsZType` unfold on the constant
  `Z (2*m) i = .Z`.

### Cross-commutation proof (T3, from `FourQubit_4_2_2.lean:114`)

The shape `pauli_comm_even_anticommutes` + filter equality is identical.
The only difference: the filter equals `Finset.univ` (not a small explicit
set like `{0, 1, 2, 3}`), and the cardinality is `2 * m`, which is
parametrically even.

### Logical (anti)commutation proofs (from `FourQubit_4_2_2.lean:245`)

Each `pauli_anticomm_odd_anticommutes`/`pauli_comm_even_anticommutes` +
filter-equality block from `FourQubit_4_2_2.lean` translates directly,
with two changes:
1. Replace `fin_cases i` (in the filter `ext` proof) with parametric
   `by_cases` on the three "special" qubits (`i`-lifted, `2m-2`, `2m-1`)
   plus the general case.
2. The explicit small Finset (e.g. `{3}` or `{1, 3}`) becomes a parametric
   singleton `{⟨i.val, _⟩}` or empty `∅`.

### Logical-in-centralizer proofs (from `FourQubit_4_2_2.lean:384`)

Direct pattern reuse: `mem_centralizer_iff_closure`, intro `s ∈ generators`,
`rcases` on Z/X-generator, dispatch via per-generator commutation lemma.

### StabilizerCode packaging (from `FourQubit_4_2_2.lean:447–467`)

The `logical_commute_cross` 4-tuple is the only k = 2 → k > 2 generalization
point. The `fin_cases ℓ <;> fin_cases ℓ'` from `FourQubit_4_2_2.lean:459`
**cannot** be replicated parametrically; replace with a single `refine ⟨_,_,_,_⟩`
that uses always-commute lemmas (T12a, T12b) and the conditional `i ≠ j`
lemma (T12c). See `plan.md` § T15.

### Distance proof (from `FourQubit_4_2_2.lean:534`)

```lean
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode generators
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX_1, (logicalOps4_2_2 0).xOp_nontrivial, by decide⟩
```

Translates almost verbatim to the iceberg's parametric form, with `by decide`
on the weight-2 fact replaced by a parametric weight computation.

### Parametric proof discipline (from `Codes/Repetition/N.lean`,
`Codes/Small/QuantumHamming.lean`, `Codes/RotatedSurface/N.lean`)

- `[Fact (2 ≤ m)]` instance, mirroring `[Fact (3 ≤ L)]` in
  `RotatedSurfaceCodeN.lean:48`.
- Parametric `noncomputable def stabilizerGroup (m : ℕ) [Fact ...]`,
  mirror `RepetitionCodeN.lean:388`.
- Per-row check-matrix decomposition for `rowsLinearIndependent` (T8),
  mirror `RepetitionCodeN.lean:219`.
- The `Subgroup.forall_comm_closure_iff` + `intro s hs` pattern for
  centralizer membership, mirror `RepetitionCodeN.lean:398`.

## New per-code definitions

These have **no direct analog** in the repo and must be defined fresh:

- **`logicalX m i`, `logicalZ m i`** for `i : Fin (2m - 2)`. The
  per-logical-qubit operators with `Fin (2m-2) ↪ Fin (2m)` lifting and
  the "X-anchor at qubit `2m-1`, Z-anchor at qubit `2m-2`" convention.
  Closest existing similar: `FourQubit_4_2_2.lean:227, 231, 235, 239`
  (logicalX_1, logicalX_2, logicalZ_1, logicalZ_2) — but those are
  hand-tuned for `m = 2` with explicit qubit indices.

- **Parametric `Fin (2m-2)` → `Fin (2m)` coercion**. Either
  `Fin.castLE (by omega : 2m - 2 ≤ 2m)` or explicit
  `⟨i.val, by have : Fact (2 ≤ m) := inferInstance; omega⟩`. The
  explicit form is more readable in the skeleton; we'll prefer it.

- **Parametric all-X / all-Z commutation lemma** (T3). Could be moved
  later to `Foundations/BinarySymplectic/SymplecticInner.lean` as a
  dual to the existing `allX_allZ_anticommute` (which handles odd `n`).
  For now, keep it private inside the iceberg file; revisit in a separate
  cleanup PR.

- **Parametric weight of weight-2 logical operator** (T18 witness). The
  fact `weight (logicalX m 0) = 2` for symbolic `m`. Could become a small
  generic helper `NQubitPauliOperator.weight_set_set_of_ne` showing
  `weight ((identity n).set i P |>.set j Q) = (1 if P ≠ I) + (1 if Q ≠ I)`
  when `i ≠ j`. Investigate whether a similar helper already exists
  during Stage 4.

- **Parametric `logicalOpsIceberg : Fin (2m-2) → LogicalQubitOps ...`**.
  Mirror `logicalOps4_2_2 : Fin 2 → LogicalQubitOps 4 ...` from
  `FourQubit_4_2_2.lean:438`. The parametric form uses a single
  uniform `fun i => ⟨logicalX m i, logicalZ m i, ...⟩` rather than the
  hand-matched `match ℓ with | 0 => ... | 1 => ...` from the m = 2 case.

# Formalization plan: [[4,2,2]] Four-qubit code

## Strategy summary

Direct instance of the CSS-stabilizer formalization pattern from
`Steane7.lean`, scaled down to 4 qubits with 2 stabilizer generators (one Z,
one X) and 4 logical operators (X̄₁, X̄₂, Z̄₁, Z̄₂). The distance proof is by
finite enumeration over the 12 weight-1 Paulis × 4 phase choices; should
close with `decide` or `native_decide` given how small the search space is.
The main novelty vs. existing files is the **k = 2** packaging: this is the
first code in the repo that exercises `logical_commute_cross` non-trivially.

## Theorem dependency graph

```
T1 (ZGenerators ZType)     T2 (XGenerators XType)
                ↓                ↓
        T3 (Z-X cross-comm)
                ↓
        T4 (all commute) ← also needs T1, T2
                ↓
        T5 (no −I) ← needs T1, T2, T3
        T6 (independent) — independent (uses decide)
        T7 (all phase 0) — independent

  T8 (X̄_ℓ Z̄_ℓ anti)    T9 (off-diagonal logicals commute)
        ↓                    ↓
  T10 (X̄_ℓ ∈ centralizer)    T11 (Z̄_ℓ ∈ centralizer)
        ↓                    ↓
            T12 (StabilizerCode pkg) ← needs T4–T11
                ↓
            T13 (HasCodeDistance = 2) ← needs T12 and finite enumeration
```

## Per-theorem proof sketch

### T1: ZGenerators_are_ZType
- Approach: case-bash on the singleton `{Z1}` via the Steane7 pattern, using
  `fin_cases` + `simp [PauliOperator.IsZType, Z1, NQubitPauliOperator.set,
  NQubitPauliOperator.identity]`.
- Existing lemmas: `PauliOperator.IsZType` definition + `Z1` unfolding.
- Difficulty: trivial.

### T2: XGenerators_are_XType
- Analogous to T1. Difficulty: trivial.

### T3: Z1_comm_X1 / ZGenerators_commute_XGenerators
- Approach: `pauli_comm_even_anticommutes` (custom tactic in
  `PauliGroup/CommutationTactics.lean`) gives us the goal "count of
  anticommuting qubits is even". The anticommute set is `{0,1,2,3}` (all 4
  qubits have X meeting Z), so cardinality 4 ⇒ even ⇒ `decide`.
- Existing lemmas: `pauli_comm_even_anticommutes` tactic; same template as
  Steane7 lines 136–224.
- Difficulty: trivial.

### T4: generators_commute
- Approach: union case-split → reduce to T1/T2/T3 via
  `CSSCommutationLemmas.ZType_commutes` / `XType_commutes`. Pattern from
  Steane7:260.
- Difficulty: trivial-to-standard.

### T5: negIdentity_not_mem
- Approach: directly invoke
  `CSS.negIdentity_not_mem_closure_union` with T1, T2, T3. Steane7:277 is the
  template.
- Difficulty: trivial.

### T6: rowsLinearIndependent_generatorsList
- Approach: `decide` (or `native_decide` if the kernel reduction is too slow).
  Check matrix is 2 × 8 over ℤ/2; trivially independent.
- Difficulty: trivial.

### T7: AllPhaseZero_generatorsList
- Approach: literal unfolding — every generator has `phasePower = 0`. Same
  pattern as Steane7:320 but only two `cons` cases.
- Difficulty: trivial.

### T8: logicalX_ℓ_anticommutes_logicalZ_ℓ (one per ℓ ∈ {1, 2})
- Approach: use `commutes_iff_even_anticommutes`'s contrapositive, or build
  directly from the operator-level anticommute lemma. We have 4 separate
  weight-2 lemmas:
  - `IXIX vs IIZZ`: anti at qubit 3 only ⇒ odd ⇒ anticommute.
  - `IIXX vs IZIZ`: anti at qubit 3 only ⇒ odd ⇒ anticommute.
- Pattern: similar to Steane7's `logicalX_anticommutes_logicalZ` but for
  weight-2 ops instead of weight-7. Will likely need a `decide`-friendly
  formulation.
- Existing lemmas: `NQubitPauliGroupElement.Anticommute` definition;
  `anticommutesAt`-based enumeration.
- Difficulty: trivial (small `decide` over Fin 4).

### T9: off-diagonal commutation (four pairs)
- Approach: `pauli_comm_even_anticommutes` + explicit `hfilter` finset
  enumeration (Steane7 pattern). Each pair has 0 or 2 anticommuting positions.
  Four pairs total: (X̄₁,X̄₂), (X̄₁,Z̄₂), (X̄₂,Z̄₁), (Z̄₁,Z̄₂).
- Note: this is the new k=2 part that has no Steane7 analog (there
  off-diagonal is vacuous via `Subsingleton.elim`).
- Difficulty: standard, but each lemma is short.

### T10: logicalX_ℓ_mem_centralizer (one per ℓ ∈ {1, 2})
- Approach: as in Steane7's `logicalX_mem_centralizer` (line 413). Use
  `mem_centralizer_iff` + `Subgroup.forall_comm_closure_iff` + case split on
  the generator. Only two generators ⇒ two commutation lemmas per logical.
- Each sub-lemma uses `pauli_comm_componentwise` (when both ops are pure X or
  pure Z, e.g. X̄_ℓ vs XXXX) or `pauli_comm_even_anticommutes` (X̄_ℓ vs ZZZZ).
- Difficulty: standard.

### T11: logicalZ_ℓ_mem_centralizer
- Analogous to T10.

### T12: stabilizerCode : StabilizerCode 4 2
- Approach: build via the struct literal, same shape as Steane7:501. The
  `logicalOps : Fin 2 → LogicalQubitOps 4 S` is a two-branch `match`/`fun`:
  ```lean
  fun ℓ => match ℓ with
    | 0 => ⟨logicalX_1, logicalZ_1, ..., ..., logicalX_1_anti_logicalZ_1⟩
    | 1 => ⟨logicalX_2, logicalZ_2, ..., ..., logicalX_2_anti_logicalZ_2⟩
  ```
  And `logical_commute_cross` invokes T9.
- Difficulty: standard (mechanical packaging).

### T13: HasCodeDistance stabilizerCode 2
- Approach: `hasCodeDistance_of` (CodeDistance.lean:54).
  - `hd : 2 ≥ 1` by `decide`.
  - `h_witness` = X̄₁ at weight 2: use `LogicalQubitOps.xOp_nontrivial` for
    nontriviality, `weight = 2` by `decide`.
  - `h_min`: for `w = 1`, every weight-1 Pauli is not a logical. Two routes:
    (a) **enumerate** all 12 weight-1 operator-parts + show each anticommutes
        with a stabilizer; conclude via
        `anticommutes_imp_not_isPauliLogicalOperator` → not in centralizer →
        not nontrivial.
    (b) **decide directly** on the full statement via `native_decide` if the
        check matrix is reachable.
  - Method (a) is cleaner; method (b) is shorter if the kernel can chew
    through it. Try (b) first; fall back to (a).
- Existing lemmas: `anticommutes_imp_not_isPauliLogicalOperator`
  (LogicalOperators.lean:46); `IsNontrivialLogicalOperator_iff`.
- Difficulty: **the hardest theorem in the file**, but still small. Estimated
  60–100 lines including the weight-1 enumeration.

## Risk register

- **Risk 1: `logical_commute_cross` field shape.** This is the first code with
  k ≥ 2, so the structure-field experience is uncharted. The field signature
  is awkward — it's a single ∀-conjunction over four equations, not a clean
  ∀-quantified equation. Mitigation: build the proof out of the four T9
  lemmas + an `omega`-style fin-case-split on ℓ, ℓ′.
- **Risk 2: `decide` blowup on T13.** If `native_decide` is too slow on
  `HasCodeDistance` directly, fall back to the manual enumeration via
  `anticommutes_imp_not_isPauliLogicalOperator`. We have a precedent in
  `RepetitionCode3.lean` for handling distance-from-enumeration, though
  `RepetitionCode3.lean:Z_on_qubit2_operators_ne_of_mem` uses the
  `sympSpan`/Submodule.mem_span machinery — that may be needed here too if
  the simpler approach fails.
- **Risk 3: Codeword-basis cross-check.** As noted in `informal_spec.md`,
  the choice of `(X̄₁, X̄₂, Z̄₁, Z̄₂) = (IXIX, IIXX, IIZZ, IZIZ)` is locked to
  the specific codeword basis quoted from EC Zoo. If Stage-3 review against
  the original 1996 papers finds a different basis labeling, all logical-op
  definitions and T8–T11 statements will need to be regenerated — but the
  proof techniques are identical.
- **Risk 4: Linter on the new file.** `linter.flexible` may flag a
  `simp_all +decide` in the T13 enumeration; will need the MCP union trick
  from CLAUDE.md if so. Not a Stage-2 concern.

## Estimated effort

- **~300 LoC** total (matches scoring.yaml estimate). Steane7.lean is 515 LoC
  for k=1 and 7 qubits with 6 generators; we have 4 qubits, 2 generators,
  but k=2 (4 logical ops + cross commutation), so the LoC counts roughly
  balance.
- **~6–8 hours** of focused proof work for Stage 4 (the human-in-the-loop or
  proof-filling agent).
- **Longest single theorem**: T13 (distance) at ~80 LoC.
- **Total `sorry`s**: ~15 (one per generator-typing, one per cross-commutation,
  one per logical commutation, plus a few structural).

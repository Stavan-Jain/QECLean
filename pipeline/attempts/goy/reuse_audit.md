# Reuse audit: Ganti-Onunkwo-Young `[[6r, 2r, 2]]`

## Directly applicable (use as-is)

### From `Framework/Core/`

- `NQubitPauliGroupElement n` — physical Pauli group on `n = 6r` qubits.
- `NQubitPauliOperator n`, `.set`, `.identity` — qubit-by-qubit construction
  of operator parts.
- `Subgroup.closure`, `Subgroup.mem_closure_iff`, `Subgroup.forall_comm_closure_iff` — group-theoretic plumbing.
- `StabilizerGroup n`, `mkStabilizerFromGenerators`, `StabilizerGroup.toSubgroup` — bundled stabilizer.
- `StabilizerCode n k`, `LogicalQubitOps`, `StabilizerCodeWithDistance n k d` — bundled code.
- `StabilizerGroup.mem_centralizer_iff_closure` (in `Centralizer.lean:107`) —
  the closure-form centralizer iff (used in T17, T18).
- `IsNontrivialLogicalOperator` (in `LogicalOperators.lean`) — the
  centralizer + non-stabilizer + non-stabilizer-equivalent predicate.
- `IsXTypeElement`, `IsZTypeElement` (in `CSS/CSSPredicates.lean`) — feed
  the CSS commutation shortcuts.
- `CSSCommutationLemmas.XType_commutes`, `.ZType_commutes` (in
  `CSS/CSSCommutationLemmas.lean`) — the trivial commutations between
  same-type elements.
- `CSS.negIdentity_not_mem_closure_union` (in `CSS/CSSNoNegI.lean`) — the
  −I-not-in-closure argument for CSS codes.
- **`hasCodeDistance_two_of_anticommute_witness`** (in
  `CSS/CSSDistance.lean:165`) — **the canonical distance-2 closer**, used
  at T22. This is the PR #34 helper.
- `weightOneAt` (in `CSS/CSSDistance.lean:26`) — the weight-1 single-qubit
  Pauli at qubit `i` with Pauli `P`.
- `weight_ofOperator`, `support_ofOperator` (in
  `PauliGroup/NQubitElement.lean:359-364`) — weight calculation simp lemmas.
- `Anticommute`, `anticommutesAt` — Pauli (anti)commutation.

### From `Foundations/`

- `pauli_comm_componentwise` (tactic in `PauliGroup/CommutationTactics.lean:36`)
  — closes commute goals when operators are disjoint or same-type.
  **Important caveat**: it uses `fin_cases i`, so it does NOT work
  parametrically — for parametric proofs we use the underlying
  `commutes_of_componentwise_commutes` with `intro k; ...` directly.
- `commutes_of_componentwise_commutes` (in
  `PauliGroup/Commutation.lean:78`) — the manual-intro alternative for
  parametric cases. Used heavily in T16a/b, T17 (logicalX vs ZLink), etc.
- `pauli_comm_even_anticommutes` (tactic in `CommutationTactics.lean:54`)
  — reduces commute goals to "even number of anticommuting qubits". Works
  parametrically (no `fin_cases`).
- `pauli_anticomm_odd_anticommutes` (tactic in `CommutationTactics.lean:66`)
  — same for anticommute. Used at T15.
- `NQubitPauliGroupElement.commutes_iff_even_anticommutes` — the underlying
  lemma `pauli_comm_even_anticommutes` calls.
- `NQubitPauliGroupElement.anticommutesAt`, `anticommutes_iff_odd_anticommutes` — basic Pauli (anti)commutation.

### From `BinarySymplectic/`

- `NQubitPauliGroupElement.rowsLinearIndependent`, `rowsLinearIndependent_iff_forall`
  (in `CheckMatrix.lean:37` + `CheckMatrixDecidable.lean:24`) — linear
  independence on the check matrix; iff form used in T12.
- `NQubitPauliGroupElement.checkMatrix`, `.toSymplectic_X_part`, `.toSymplectic_Z_part`
  — explicit column evaluation for parametric T12.
- `GeneratorsIndependent`, `GeneratorsIndependent_of_rowsLinearIndependent`
  — bundled-form independence.
- `NQubitPauliGroupElement.AllPhaseZero` (with `_cons`, `_nil`) — phase-zero
  predicate on lists.

## Lightly adapted (existing pattern, new instance)

### From `Iceberg/N.lean` (the closest template, ~70-80% reuse expected)

- **Index helper pattern**: `Iceberg/N.lean:106-119` defines `logIdx`, `zAnchor`, `xAnchor`
  as `@[inline] private def` with `omega`-discharged bound proofs. We adapt to
  `qubit_x`, `qubit_0`, `qubit_z`, `linkIdx`, `linkIdxSucc`. Same exact pattern.

- **Distinctness lemma pattern**: `Iceberg/N.lean:397-419` (`logIdx_ne_xAnchor`,
  `logIdx_ne_zAnchor`, `xAnchor_ne_zAnchor`) proves Fin-index distinctness
  via `congrArg Fin.val` + `omega`. We adapt to ~9 distinctness lemmas
  (3 pairs of `qubit_x/0/z`, plus link-related).

- **`pauli_comm_even_anticommutes` + filter-equality pattern**:
  `Iceberg/N.lean:180-193` (T3 `S_Z_comm_S_X`). We adapt this 4x for T7a-d.

- **`pauli_anticomm_odd_anticommutes` + singleton-filter pattern**:
  `Iceberg/N.lean:421-453` (T11 `logicalX_anticommutes_logicalZ_diag`).
  Adapted to T15 with the same 4-way `by_cases` on qubit role.

- **Centralizer membership via `forall_comm_closure_iff` + per-generator dispatch**:
  `Iceberg/N.lean:575-601` (T13/T14). We adapt to a 4-way dispatch (4 generator
  types: XLink, XBig, ZLink, ZBig) instead of iceberg's 2-way.

- **Parametric weight-1 anti-witness pattern**: `Iceberg/N.lean:706-721` (T17).
  Iceberg uses a 3-way Pauli match (X, Y, Z) with each branch picking the
  appropriate full-support stabilizer. We extend with a mod-3 trichotomy on
  the qubit role.

- **`hasCodeDistance_two_of_anticommute_witness` invocation**:
  `Iceberg/N.lean:746-755` (T18). Direct adaptation to our T22.

- **`weight_logicalX` parametric weight lemma**: `Iceberg/N.lean:725-744` (the
  weight-2 helper for the witness side of T18). Adapt to our `logicalX r 0`
  which has weight 2 (X at qubits 0 and 1).

- **Structural-refine `logical_commute_cross`**: `Iceberg/N.lean:628-633`
  (T15 packaging). Direct adaptation — same 4-tuple structure.

- **`stabilizerCode_toSubgroup_eq` pattern**: `Iceberg/N.lean:638-643` (T16).
  One-line `change` + `rw [listToSet_generatorsList]`.

### From `Codes/Small/SixQubit_6_2_2.lean`

- **Multi-Z trichotomy weight-1 anti-witness** (T31 in C_6, `lean-patterns.md`
  § "Multiple Z-generators... with overlapping qubit supports"). C_6 uses a
  3-way `hi_trichotomy`; we use a 3-way mod-3 trichotomy on `i.val mod 3`.
  Same pattern, different decomposition.

- **k=2 `logical_commute_cross` dispatch**: SixQubit_6_2_2.lean uses
  `fin_cases ℓ <;> fin_cases ℓ'` (works because `Fin 2` is concrete). We
  cannot use this for `Fin (2r)`; instead use Iceberg's structural-refine
  pattern.

- **`pauli_comm_componentwise` for disjoint mixed-type cases** (the
  `lean-patterns.md` note): logicalX vs ZLink is X vs Z, but disjoint
  supports. The tactic handles this — we use it.

### From `Codes/Small/CSS_4_1_2.lean`

- **Helper-lemma pattern with `hi : i = q0 ∨ i = q1 ∨ ...` disjunction**:
  for the weight-1 anti-witness helpers when the witness generator's support
  is a subset (e.g., `ZLink` covers only 2 z-qubits, not all). Used at T21.

### From `Codes/Repetition/N.lean`

- **`[Fact (...)]` discipline for parametric bounds**: every Fin coercion
  uses `have := Fact.out (p := (1 ≤ r))` + `omega`. We adopt this style.

### From `Codes/RotatedSurface/N.lean`

- **Avoid `fin_cases` over parametric `Fin (parametric_expr)`**: all
  parametric-index proofs use `Fin.ext_iff` + `omega`. Standard discipline.

## New per-code definitions (no analog in repo)

- **Qubit role decomposition `q.val mod 3 ∈ {0, 1, 2}`**: GOY's
  three-qubits-per-row structure is unique. The mod-3 trichotomy is the
  first appearance of this pattern in the repo.
- **`qubit_x`, `qubit_0`, `qubit_z`**: 3-way splitter of `Fin (6r)`.
- **`linkIdx`, `linkIdxSucc`**: 2-way splitter of `Fin (2r - 1)` into
  `Fin (2r)`.
- **`XLink`, `XBig`, `ZLink`, `ZBig`**: 4 distinct generator types (vs.
  iceberg's 2 and Knill C_6's homogeneous-weight 4).
- **`coveringXLink`, `coveringZLink`**: row-to-link covering functions
  used in T21. May be a candidate for promotion to `Geometry/`.
- **`weight_logicalX`**: parametric weight-2 calculation for GOY's
  `logicalX r 0`. Same shape as iceberg's `weight_logicalX` but with
  different qubit positions (qubits 0 and 1 instead of 0 and 2m-1).

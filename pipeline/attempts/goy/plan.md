# Formalization plan: Ganti-Onunkwo-Young `[[6r, 2r, 2]]`

## Strategy summary

GOY is a **parametric CSS family** with `4r` generators of two distinct
weights (weight-2 link generators + weight-4r "big" generators), and `2r`
logical qubits. The skeleton structure mirrors `Iceberg/N.lean` (the only
existing parametric `k ≥ 2` formalization in the repo), but with:

- **4 generator types** (`XLink`, `XBig`, `ZLink`, `ZBig`) instead of 2.
- **2r logical-qubit indices** (vs. iceberg's `2m - 2`).
- **Variable-weight stabilizers** (2 and 4r vs. iceberg's uniform 2m).
- **Mod-3 trichotomy** in the weight-1 anti-witness function (vs. iceberg's
  trivial witness-by-Pauli-class).

The distance proof rides on the PR #34 helper
`hasCodeDistance_two_of_anticommute_witness`. The hardest part is the
generator-independence proof (T12) at `4r × 12r` check-matrix scale.

## Theorem dependency graph

```
T1 (ZLink Z-type)  ────┐
T2 (ZBig  Z-type)  ────┼─→ T5 (Z-gens are Z-type) ────┐
                       │                              │
T3 (XLink X-type)  ────┼─→ T6 (X-gens are X-type) ────┤
T4 (XBig  X-type)  ────┘                              │
                                                      ├─→ T8 (all-pair commute) ──┐
T7a (ZLink·XLink)  ────┐                              │                            │
T7b (ZLink·XBig)   ────┼─→ T7 (Z-gen·X-gen commute) ──┘                            ├─→ T9 (-I not in S)
T7c (ZBig·XLink)   ────┤                                                           │
T7d (ZBig·XBig)    ────┘                                                           └─→ T13 (StabilizerGroup)

T10 (listToSet) ────────────────────────────────────────→ T13 ────→ T14 (toSubgroup_eq)
T11 (phase 0)   ────────────────────────────────────────────────────→ T19 (StabilizerCode)
T12 (independence) ─────────────────────────────────────────────────→ T19
T13, T14        ────────────────────────────────────────→ T17, T18 (logicals in centralizer)
                                                                    └─→ T19

T15 (logicalX⊥logicalZ diag) ──→ T19
T16 (logical off-diag commute) ─→ T19

T19 ──→ T20 (stabilizerCode_toSubgroup_eq)
T19, T21 (anti-witness) ──→ T22 (HasCodeDistance 2)
T19, T22 ──→ T23 (StabilizerCodeWithDistance)
```

## Per-theorem proof sketch

### Index helpers (`@[inline] private def`s)

Five helpers; all closure by `omega` from `[Fact (1 ≤ r)]`:

```lean
@[inline] private def qubit_x {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    Fin (6 * r) :=
  ⟨3 * i.val, by have := Fact.out (p := (1 ≤ r)); have := i.isLt; omega⟩

@[inline] private def qubit_0 {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    Fin (6 * r) :=
  ⟨3 * i.val + 1, by ...⟩

@[inline] private def qubit_z {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r)) :
    Fin (6 * r) :=
  ⟨3 * i.val + 2, by ...⟩

@[inline] private def linkIdx {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    Fin (2 * r) :=
  ⟨i.val, by have := Fact.out (p := (1 ≤ r)); have := i.isLt; omega⟩

@[inline] private def linkIdxSucc {r : ℕ} [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    Fin (2 * r) :=
  ⟨i.val + 1, by have := Fact.out (p := (1 ≤ r)); have := i.isLt; omega⟩
```

**Distinctness lemmas**: `qubit_x i ≠ qubit_0 i`, etc. — proved via
`Fin.ext_iff` + `omega` (since `3i ≠ 3i+1 ≠ 3i+2 mod`-anything works).
Also `qubit_x i ≠ qubit_x j` when `i ≠ j` (same `Fin.ext_iff` + `omega`).

- **Approach**: mechanical `omega`.
- **Difficulty**: trivial.
- **LoC estimate**: ~50 (5 defs + ~9 distinctness lemmas).

### T1 (ZLink Z-type)

For each `i : Fin (2r - 1)`, `IsZTypeElement (ZLink r i)` (Z at qubit_z i
and qubit_z (i+1), I elsewhere).

```lean
lemma ZLink_isZType (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    IsZTypeElement (ZLink r i) := by
  refine ⟨rfl, ?_⟩
  intro j
  -- Per-qubit: either j is qubit_z linkIdx or qubit_z linkIdxSucc (then Z), else I.
  simp only [ZLink, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  split_ifs <;> simp [PauliOperator.IsZType]
```

- **Approach**: split on qubit-position match; `IsZType` holds for `I` and
  `Z` per case.
- **Difficulty**: trivial.

### T2 (ZBig Z-type)

`IsZTypeElement (ZBig r)`. Use `commutes_of_componentwise_commutes`-style
intro `k`, then case analysis on `k.val mod 3`:

```lean
lemma ZBig_isZType (r : ℕ) [Fact (1 ≤ r)] :
    IsZTypeElement (ZBig r) := by
  refine ⟨rfl, ?_⟩
  intro k
  -- ZBig has Z at all qubits with k.val mod 3 ∈ {0, 1}, I at k.val mod 3 = 2.
  simp only [ZBig, ...]
  -- Either k.val mod 3 = 0/1 (Z) or = 2 (I); IsZType holds for both.
  sorry  -- TODO(goy-T2): mod-3 case analysis
```

- **Approach**: direct unfolding once `ZBig` is defined; per-qubit check is
  Z or I depending on the qubit's role.
- **Difficulty**: standard parametric (the `ZBig` definition itself encodes
  the role check; the IsZType proof becomes mechanical).
- **Risk**: depends on how `ZBig` is constructed — if as a `Finset.fold` over
  rows, the per-qubit check needs that-specific simp lemma.

### T3, T4 (XLink, XBig X-type)

Mirror of T1, T2 with Z↔X swap.

### T5 (Z-generators set is Z-type)

`∀ g ∈ ZGenerators r, IsZTypeElement g`. The set is `{ZLink i : i ∈ Fin (2r-1)} ∪ {ZBig}`.
Case split: if `g = ZLink i`, apply T1; if `g = ZBig`, apply T2.

- **Approach**: `rcases (Set.mem_union ...).mp hg` + dispatch.
- **Difficulty**: trivial.

### T6 (X-generators set is X-type)

Mirror of T5.

### T7a (ZLink i · XLink j: commute)

ZLink has Z at z-qubits, XLink has X at x-qubits — disjoint (mod-3 roles differ).
Use `pauli_comm_componentwise` (works for disjoint supports per the C_6
Stage 6 pattern note).

```lean
private lemma ZLink_comm_XLink (r : ℕ) [Fact (1 ≤ r)]
    (i j : Fin (2 * r - 1)) :
    ZLink r i * XLink r j = XLink r j * ZLink r i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  -- At every qubit, either ZLink has I (and any X commutes with I) or XLink
  -- has I (similar).
  simp only [ZLink, XLink, ...]
  split_ifs <;> simp [PauliOperator.mulOp]
```

- **Approach**: componentwise, no anticomm filter needed.
- **Difficulty**: standard.
- **Risk**: lots of `split_ifs` cases (4 from ZLink × 4 from XLink); `simp`
  may need help.

### T7b (ZLink i · XBig: commute)

ZLink has Z at qubits {qubit_z linkIdx i, qubit_z linkIdxSucc i}; XBig has
X at all 0- and z-qubits, including these two z-qubits. So the anticomm
support is exactly these two z-qubits — count 2, even.

```lean
private lemma ZLink_comm_XBig (r : ℕ) [Fact (1 ≤ r)] (i : Fin (2 * r - 1)) :
    ZLink r i * XBig r = XBig r * ZLink r i := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
        (anticommutesAt (ZLink r i).operators (XBig r).operators)) =
        ({qubit_z (linkIdx i), qubit_z (linkIdxSucc i)} : Finset (Fin (6 * r))) := by
    ext k
    -- Per-qubit case analysis.
    sorry  -- TODO(goy-T7b): filter equality
  rw [hfilter]
  rw [Finset.card_insert_of_notMem (by ...), Finset.card_singleton]
  exact even_two
```

- **Approach**: filter-equality via `by_cases k = qubit_z linkIdx i`,
  `by_cases k = qubit_z linkIdxSucc i`, then else-branch.
- **Difficulty**: standard parametric (~30 LoC).

### T7c (ZBig · XLink j: commute)

Mirror of T7b. Anticomm support: {qubit_x linkIdx j, qubit_x linkIdxSucc j}, count 2.

### T7d (ZBig · XBig: commute) — the **iceberg-defining property**

ZBig has Z at all x- and 0-qubits (4r qubits); XBig has X at all 0- and
z-qubits (4r qubits). Overlap = 0-qubits = {qubit_0 j : j ∈ Fin (2r)}, count 2r.
For `r ≥ 1`, 2r is even. ✓

```lean
private lemma ZBig_comm_XBig (r : ℕ) [Fact (1 ≤ r)] :
    ZBig r * XBig r = XBig r * ZBig r := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter ...) =
        (Finset.univ.image qubit_0 : Finset (Fin (6 * r))) := by
    ext k
    -- k is in the filter iff k.val mod 3 = 1 (it's a 0-qubit).
    sorry  -- TODO(goy-T7d): filter = image qubit_0
  rw [hfilter]
  rw [Finset.card_image_of_injective _ qubit_0_injective, Finset.card_univ,
    Fintype.card_fin]
  exact ⟨r, by ring⟩
```

- **Approach**: filter = image of `qubit_0`; cardinality = 2r (image of
  injective from `Fin (2r)`). Even because `2r = 2 * r`.
- **Difficulty**: medium. Need `qubit_0` injective + `Finset.card_image_of_injective`.
- **LoC estimate**: ~40.

### T7 (cross-commute)

4-way `rcases` on Z-vs-X membership, dispatching to T7a-d.

### T8 (all-pair commute)

CSS structural argument, T5 + T6 + T7.

### T9 (`−I` not in subgroup)

Standard via `CSS.negIdentity_not_mem_closure_union` consuming T5, T6, T7.

### T10 (listToSet equality)

```lean
def generatorsList (r : ℕ) [Fact (1 ≤ r)] : List (NQubitPauliGroupElement (6 * r)) :=
  (List.finRange (2 * r - 1)).map (ZLink r) ++ [ZBig r] ++
  (List.finRange (2 * r - 1)).map (XLink r) ++ [XBig r]

-- length = (2r - 1) + 1 + (2r - 1) + 1 = 4r = n - k.
```

- **Risk**: the natural list-construction has `(2r - 1) + 1 + (2r - 1) + 1` length,
  which must be proved equal to `n - k = 4r`. Use `omega` after `simp [length, ...]`.

### T11 (AllPhaseZero)

The list `generatorsList r` is built from `List.map` + concatenations of
constructors with `phasePower = 0`. Proof: induction on the list or direct
unfolding. Likely closeable by `simp [AllPhaseZero, generatorsList, ...]`.

- **Risk**: `AllPhaseZero` may not have a clean simp normal form for
  `List.map`; backup is manual induction on `Fin (2r - 1)`.

### T12 (Generator independence — the hardest theorem)

The `4r × 12r` check matrix has the structure:

```
         | X-part (cols 0..6r-1)   | Z-part (cols 6r..12r-1) |
---------+-------------------------+--------------------------+
ZLink 0  | 0...0                   | 0..0 1 0..0 1 0..0       |  -- ones at qubit_z 0 and qubit_z 1
ZLink 1  | 0...0                   | 0..0 1 0..0 1 0..0       |  -- ones at qubit_z 1 and qubit_z 2
 ...     | ...                     | ...                      |
ZLink (2r-2) | 0...0                | ones at qubit_z (2r-2), (2r-1) |
ZBig     | 0...0                   | ones at x- and 0-qubits  |  -- 4r ones
XLink 0  | ones at qubit_x 0, 1    | 0...0                    |
 ...     | ...                     | ...                      |
XLink (2r-2) | ones at qubit_x (2r-2), (2r-1) | 0...0           |
XBig     | ones at 0- and z-qubits | 0...0                    |  -- 4r ones
```

The Z-half rows (ZLinks + ZBig) only have X-part entries... wait, **invert**:
in the symplectic check matrix, a **Z-stabilizer** has nonzero entries in
the **Z-part** of the matrix (columns 6r..12r-1) and zeros in the X-part.
Conversely, X-stabilizers have nonzero entries in the X-part.

So the check matrix splits **block-diagonally**:

```
         | X-cols    | Z-cols                  |
---------+-----------+-------------------------+
Z-gens   | 0         | (2r × 6r matrix; let's call it M_Z)  |
X-gens   | (2r × 6r matrix; M_X) | 0           |
```

where M_Z has rows {ZLink 0, ..., ZLink (2r-2), ZBig} (2r rows) and
similarly M_X. **Independence of the full 4r × 12r matrix reduces to
independence of M_Z and M_X separately**. By the symmetry of the
construction (the Z-side and X-side are mirror images of each other under
the qubit-role swap), it suffices to prove independence of M_Z.

**M_Z structure** (2r rows × 6r columns):

| Row     | Columns: x-qubits (0-2r-1) | 0-qubits (2r..4r-1) | z-qubits (4r..6r-1) |
|---------|----------------------------|---------------------|----------------------|
| ZLink i | 0                          | 0                   | 1 at z-qubits {i, i+1} |
| ZBig    | 1 at all x-qubits          | 1 at all 0-qubits   | 0                    |

Wait — actually let me re-check column ordering. The `Fin (6r)` columns are
in `qubit_x | qubit_0 | qubit_z` row-major order if we list by qubit
index — but the matrix columns are in 0..6r-1 order, so they go
qubit-index 0 (= qubit_x 0), 1 (= qubit_0 0), 2 (= qubit_z 0), 3 (= qubit_x 1),
... i.e., x-, 0-, z- alternate.

For clarity: let `q ∈ Fin (6r)`. Then `q.val mod 3` selects the role; for
each row `j ∈ Fin (2r)`, the three qubits at `{3j, 3j+1, 3j+2}` are
{qubit_x j, qubit_0 j, qubit_z j}.

**Block structure of M_Z (the Z-part of the check matrix), indexing
by qubit role**:

| Row     | qubit_x q's (mod-3 = 0) | qubit_0 q's (mod-3 = 1) | qubit_z q's (mod-3 = 2) |
|---------|--------------------------|--------------------------|--------------------------|
| ZLink i | 0                        | 0                        | 1 at j = i, j = i+1     |
| ZBig    | 1 (all)                  | 1 (all)                  | 0                       |

So:
- **Among ZLinks**: 2r-1 rows, each with two nonzero entries in the z-qubit block.
  Specifically, ZLink i has 1's at z-qubits {i, i+1}. **This is the
  incidence matrix of a path graph on 2r vertices** (z-qubit indices).
  These 2r-1 rows are linearly independent iff the graph has no cycles —
  which a path doesn't.
- **The ZBig row** lives entirely in the x- and 0-qubit blocks, with zero
  entries in the z-qubit block. So it's independent of any combination of
  ZLink rows: the combination would have 0's in the x- and 0-qubit blocks,
  but ZBig has 1's there.

**Independence proof strategy**:

1. Show: if a linear combination `∑ a_i (ZLink i) + b · ZBig = 0`, then
   `b = 0` (by looking at any x-qubit column: only ZBig has a 1, so
   `b = 0`).
2. With `b = 0`, the combination is `∑ a_i (ZLink i) = 0` — a chain
   identity. Show inductively that `a_0 = a_1 = ... = a_{2r-2} = 0`:
   - z-qubit 0 column: only `ZLink 0` has a 1 ⇒ `a_0 = 0`.
   - z-qubit 1 column: only `ZLink 0` and `ZLink 1` have 1's ⇒ `a_0 + a_1 = 0` ⇒ `a_1 = 0`.
   - ... cascade ...

**Estimated LoC**: ~80-100 (the longest proof in the file).

### T13, T14 (StabilizerGroup packaging + toSubgroup bridge)

Standard `mkStabilizerFromGenerators` invocation; bridge via
`listToSet_generatorsList`.

### T15 (logicalX ⊥ logicalZ diagonal)

For each `i : Fin (2r)`:

```lean
theorem logicalX_anticommutes_logicalZ_diag (r : ℕ) [Fact (1 ≤ r)]
    (i : Fin (2 * r)) :
    Anticommute (logicalX r i) (logicalZ r i) := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter (anticommutesAt (logicalX r i).operators (logicalZ r i).operators))
      = ({qubit_0 i} : Finset (Fin (6 * r))) := by
    ext k
    -- 4-case by_cases on k = qubit_x i, qubit_0 i, qubit_z i, else
    sorry  -- TODO(goy-T15): filter = {qubit_0 i}
  rw [hfilter, Finset.card_singleton]
  decide
```

- **Approach**: 4-way `by_cases` on `k`'s role / row position.
- **Difficulty**: standard parametric (~25 LoC).

### T16a, T16b (logicalX·logicalX and logicalZ·logicalZ commute)

Both X-type / both Z-type, use `commutes_of_componentwise_commutes`.

### T16c (logicalX·logicalZ off-diagonal commute)

For `i ≠ j`, supports are in **disjoint rows**, so completely disjoint
qubit indices.

```lean
theorem logicalX_commutes_logicalZ_offdiag (r : ℕ) [Fact (1 ≤ r)]
    {i j : Fin (2 * r)} (hij : i ≠ j) :
    logicalX r i * logicalZ r j = logicalZ r j * logicalX r i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  -- At every qubit, either logicalX has I (k not in row i) or logicalZ has I (k not in row j).
  simp only [logicalX, logicalZ, ...]
  split_ifs <;> simp_all [PauliOperator.mulOp]  -- requires hij to discharge "both nonzero" branches
```

- **Risk**: the `split_ifs` cases include "k = qubit_x i = qubit_z j", which
  needs `hij` to rule out via `omega` (3i ≠ 3j+2 unless i = j and... actually 3i = 3j+2 has no integer solutions, so this is automatic; but Lean's split_ifs may not see this without help).
- **Difficulty**: standard parametric (~20 LoC); main friction is the
  combinatorics of `split_ifs`.

### T17, T18 (logicals in centralizer — per-generator dispatch)

Mirror of `Iceberg/N.lean` T13/T14: `mem_centralizer_iff_closure` +
`Subgroup.forall_comm_closure_iff` + per-generator dispatch via 4 helper
lemmas:

- `logicalX_commutes_XLink j`, `logicalX_commutes_XBig`: both X-type.
- `logicalX_commutes_ZLink j`: disjoint (logicalX is x- and 0-qubits;
  ZLink is z-qubits). Componentwise.
- `logicalX_commutes_ZBig`: overlap at {qubit_x i, qubit_0 i} (count 2, even).

Symmetric for `logicalZ`.

**~8 private helper lemmas** total (4 per logical type).

### T19 (StabilizerCode packaging)

Parametric `Fin (2r)` index, so the `logical_commute_cross` field uses the
`Iceberg/N.lean` structural-refine pattern:

```lean
logical_commute_cross := by
  intro ℓ ℓ' hne
  refine ⟨logicalX_commutes_logicalX r ℓ ℓ', ?_, ?_, logicalZ_commutes_logicalZ r ℓ ℓ'⟩
  · exact logicalX_commutes_logicalZ_offdiag r hne
  · exact (logicalX_commutes_logicalZ_offdiag r (Ne.symm hne)).symm
```

### T20 (stabilizerCode_toSubgroup_eq)

Trivial `change` + `rw [listToSet_generatorsList]`.

### T21 (Weight-1 anti-witness — the parametric distance step)

```lean
private lemma weight_one_anticomm_witness (r : ℕ) [Fact (1 ≤ r)] :
    ∀ i : Fin (6 * r), ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators r, Anticommute (weightOneAt i P) g := by
  intro i P hP
  -- Trichotomy on i.val mod 3 (qubit role).
  have hrole : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  -- Get the row index j = i.val / 3 : Fin (2r).
  set j : Fin (2 * r) := ⟨i.val / 3, by ...⟩ with hj_def
  rcases hrole with hr | hr | hr
  · -- mod = 0: i = qubit_x j
    ...
  · -- mod = 1: i = qubit_0 j
    ...
  · -- mod = 2: i = qubit_z j
    ...
```

For each role:

- **mod = 0** (i is x-qubit of row j):
  - `P = X` or `Y`: witness `ZBig` (Z at x-qubit).
    Anticomm filter: exactly `{i}` (every other x-qubit has I from weightOneAt).
  - `P = Z`: need an XLink covering qubit_x j. Use `XLink (min j.val (2r-2))`
    (which covers x-qubits {min j (2r-2), min j (2r-2) + 1}; this is the
    standard "every interior or boundary x-qubit is in some XLink"
    argument).

- **mod = 1** (i is 0-qubit of row j):
  - `P = X` or `Y`: witness `ZBig`.
  - `P = Z`: witness `XBig`.

- **mod = 2** (i is z-qubit of row j):
  - `P = X` or `Y`: need a ZLink covering qubit_z j (symmetric to x-qubit).
  - `P = Z`: witness `XBig`.

For the "some `XLink` covers row j" subcase, define a helper:

```lean
private def coveringXLink (r : ℕ) [Fact (1 ≤ r)] (j : Fin (2 * r)) :
    Fin (2 * r - 1) :=
  if h : j.val + 1 < 2 * r then
    ⟨j.val, by have := Fact.out (p := (1 ≤ r)); have := j.isLt; omega⟩
  else
    -- j is the last row; use the previous XLink.
    ⟨j.val - 1, by ...⟩
```

This gives an XLink whose support includes qubit_x j, with case analysis
discharging the bound proofs via `omega`.

- **Difficulty**: this is the most intricate piece, but each sub-case
  follows the iceberg/C_6 weight-1 helper pattern.
- **LoC estimate**: ~150 (4 single-Pauli witness helpers for the link
  cases × ~30 LoC each = 120, plus the trichotomy dispatch = 30).

### T22 (`HasCodeDistance 2`)

```lean
theorem code_has_distance_two (r : ℕ) [Fact (1 ≤ r)] :
    HasCodeDistance (stabilizerCode r) 2 := by
  have h1 : 1 ≤ r := Fact.out
  have h0lt : 0 < 2 * r := by omega
  refine hasCodeDistance_two_of_anticommute_witness (stabilizerCode r) (generators r)
    (stabilizerCode_toSubgroup_eq r) (weight_one_anticomm_witness r) ?_
  refine ⟨logicalX r ⟨0, h0lt⟩, ?_, ?_⟩
  · exact (logicalOpsGOY r ⟨0, h0lt⟩).xOp_nontrivial
  · exact weight_logicalX r ⟨0, h0lt⟩
```

Need a helper `weight_logicalX r i : weight (logicalX r i) = 2` — direct
parametric weight calculation. Same pattern as `Iceberg/N.lean`'s
`weight_logicalX`.

### T23 (`StabilizerCodeWithDistance`)

Trivial wrapper.

## Risk register

### Risk 1: Generator independence proof (T12) — the longest piece

The cleanest formulation is "M_Z's rows form a path-graph incidence matrix
extended with one extra row (`ZBig`) in a different block." The chain
identity proof:

1. Specialize to an x-qubit column to force `b_ZBig = 0`.
2. Specialize iteratively to z-qubit columns 0, 1, ..., 2r-1 to peel off
   `a_{ZLink 0}, a_{ZLink 1}, ..., a_{ZLink 2r-2}`.

This is a parametric inductive argument (mirroring `Repetition/N.lean`'s
3-band proof). Estimated LoC: 80-100.

**Alternative**: if the chain identity is too involved, fall back to **leaving
T12 as a `sorry` blocked on a future per-family helper** (`chainIndependence`
in `BinarySymplectic`). This would be the only blocked sorry expected.

### Risk 2: Mod-3 case analysis in many lemmas

The qubit role decomposition (`i.val mod 3`) reappears in:
- T2, T4 (ZBig, XBig Z-type / X-type)
- T7b, T7c, T7d (cross-commute filters)
- T17, T18 (logicals in centralizer)
- T21 (weight-1 anti-witness)

In each, the simp/omega flow needs to discharge `3i mod 3 = 0`, `(3i+1) mod 3 = 1`,
`(3i+2) mod 3 = 2`. **Mitigation**: define `qubit_x_mod3 : (qubit_x i).val % 3 = 0` etc.
as `simp` lemmas early in the file.

### Risk 3: `Fin (2 * r - 1)` indexing for links

`Fin (2 * r - 1)` is awkward parametrically — `fin_cases` won't reduce it.
All proofs over this index must use `Fin.ext_iff` + `omega` (same as
iceberg's `Fin (2 * m - 2)` handling).

### Risk 4: `[Fact (1 ≤ r)]` instance synthesis

The instance is declared globally for the section but specialized arguments
to `Fact.out` need to type-check. **Mitigation**: explicitly invoke via
`have h : 1 ≤ r := Fact.out` at the top of each long proof.

### Risk 5: `linkIdx j ≠ linkIdxSucc j` and similar distinctness

Many filter-equality proofs need to assert that the two link endpoints are
distinct `Fin (2r)` values. **Mitigation**: prove `linkIdx_ne_linkIdxSucc`
once globally.

### Risk 6: The "covering XLink" function (T21)

The `coveringXLink j` function needs to handle the case where `j` is the
last row (no `XLink j` exists since `2r - 1` is the max link index).
**Mitigation**: explicit `if-then-else` with omega-discharged bounds.

### Risk 7: Performance at large `r` (estimation only)

Build will only check the parametric proof structure — at no point do we
specialize to a concrete `r`. So **performance shouldn't degrade with `r`**.
But the proof terms themselves are larger than iceberg's because of the
4r generators.

## Estimated effort

| Section | LoC |
|---------|-----|
| Imports + header | 30  |
| Index helpers (qubit_x/0/z, linkIdx, distinctness) | 80 |
| Generator definitions (XLink, XBig, ZLink, ZBig) | 60 |
| Generator sets (T1-T4) | 60 |
| Z-type / X-type predicates (T5, T6) | 40 |
| Cross-commutation (T7a-d, T7) | 200 |
| All-pair commute + −I (T8, T9) | 30 |
| Generator list + listToSet (T10) | 40 |
| Phase-zero (T11) | 20 |
| Independence (T12) | **80-100** |
| StabilizerGroup (T13, T14) | 30 |
| Logical operators + (anti)commutation (T15, T16) | 100 |
| Logicals in centralizer (T17, T18) | 100 |
| StabilizerCode packaging (T19) | 40 |
| Distance bridge (T20) | 10 |
| Weight-1 anti-witness (T21) | 150 |
| HasCodeDistance (T22, T23) | 30 |
| **Total estimated LoC** | **~1100** |

This exceeds the catalog's 1500 estimate (so under budget), but is roughly
2x iceberg's `~766 LoC` for the analogous shape — accounted for by:
- 4 generator types vs. 2 ⇒ 2x cross-commute proof
- 6 weight-1 anti-witness cases vs. 3 (mod-3 trichotomy) ⇒ 2x witness LoC
- Same logical-commute structure (`Fin (2r)` ↔ `Fin (2m-2)`) so no overhead
- T12 (independence) is parametrically harder ⇒ +50 LoC

**Time estimate**: 3-4 sessions for Stage 4 (T12 alone takes 1 session;
T21 takes 1 session; T7 + everything else takes 1 session).

## Stage-3 SKIPPED

Per the task spec, Stage 3 is skipped. Our `informal_spec.md`:

1. Cites the paper's Eq. (3), (4), and §III explicitly.
2. Performs by-hand commutation verification of all stabilizer pairs,
   logical-stabilizer pairs, and logical-logical pairs in the parametric
   table.
3. Cross-checks the r=1 specialization against `SixQubit_6_2_2.lean`
   (different presentation, same code subspace).
4. Documents the qubit indexing scheme explicitly.

If the GOY r=1 commutation table failed any of the cross-checks, our spec
would be wrong; since every check passes by direct mod-3 case analysis,
the spec is sound.

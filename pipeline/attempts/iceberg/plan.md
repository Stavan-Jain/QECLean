# Formalization plan: iceberg `[[2m, 2m−2, 2]]`

## Strategy summary

The iceberg family has the simplest possible CSS structure (two generators:
`S_X = XX..X`, `S_Z = ZZ..Z`) and falls into the **parametric CSS** bucket
(parameter `m`, parameter constraint `[Fact (2 ≤ m)]`). The skeleton
mirrors `FourQubit_4_2_2.lean` for the per-generator and per-logical-operator
proofs, and lifts the indexing into a `Fin (2m − 2)`-indexed family for the
logical operators. The distance proof rides on the PR #34 helper
`hasCodeDistance_two_of_anticommute_witness` from `CSSDistance.lean`.

The single new ingredient over the existing parametric repository is the
**parametric weight-1 anticommute witness** and the **parametric all-X /
all-Z commutation for even `n`** (the iceberg-specific `n = 2m` constraint
is what makes the two stabilizers commute, which fails for the odd-`n`
case used by Steane7 / Shor9 / Repetition3).

## Theorem dependency graph

```
T1 (Z-type S_Z) ───┐
                   ├─→ T4 (all pairs commute) ──┐
T2 (X-type S_X) ───┤                            ├─→ T5 (-I not in S)
                   │                            │
T3 (S_Z S_X comm) ─┘                            └─→ T9 (StabilizerGroup)

T6 (listToSet) ─→ T9 ─→ T10 (toSubgroup_eq)

T7 (phase 0)   ─→ T15 (StabilizerCode)
T8 (independence) ─→ T15
T9, T10        ─→ T13, T14 (logicals in centralizer)
                 └─→ T15

T11 (logical X anticomm Z, diag) ─→ T15
T12 (logical off-diag commutation) ─→ T15

T15 ─→ T16 (stabilizerCode_toSubgroup_eq)
T15, T17 (anti-witness) ─→ T18 (HasCodeDistance 2)
T15, T18 ─→ T19 (StabilizerCodeWithDistance)
```

## Per-theorem proof sketch

### T1 (Z-type predicate for `S_Z m`)

```lean
intro g hg
rcases (by simpa [ZGenerators] using hg) with rfl
refine ⟨rfl, ?_⟩
intro i
exact Or.inr (by simp [S_Z, NQubitPauliOperator.Z, PauliOperator.IsZType])
```

The `NQubitPauliOperator.Z (2*m)` operator is the constant function
`fun _ => Z`, so the per-qubit `PauliOperator.IsZType (Z)` is trivial.

- **Approach**: direct unfold.
- **Difficulty**: trivial.

### T2 (X-type predicate for `S_X m`)

Mirror of T1, swap `Z ↔ X`.

### T3 (S_Z m and S_X m commute)

The interesting parametric proof. Two approaches:

**Approach A (preferred): direct `pauli_comm_even_anticommutes`.** The
filter is `Finset.univ` (every qubit anticommutes), cardinality `2m`,
which is even via `Nat.even_two_mul`.

```lean
private lemma S_Z_comm_S_X (m : ℕ) [Fact (2 ≤ m)] : S_Z m * S_X m = S_X m * S_Z m := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (S_Z m).operators (S_X m).operators)) = (Finset.univ : Finset (Fin (2 * m))) := by
    ext i
    simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
      S_Z, S_X, NQubitPauliOperator.Z, NQubitPauliOperator.X, PauliOperator.mulOp]
  rw [hfilter, Finset.card_univ, Fintype.card_fin]
  exact ⟨m, by ring⟩
```

**Approach B: lift the existing `allX_allZ_anticommute` framework.** In
`SymplecticInner.lean:106`, the all-X / all-Z anticommutation theorem
states "`Odd n` ⇒ anticommute". The natural dual ("`Even n` ⇒ commute")
might already be derivable but doesn't seem to be stated directly. We
could add a `allX_allZ_commute_of_even` lemma to `SymplecticInner.lean`,
but this is a separate cleanup; Approach A is self-contained.

- **Approach**: filter-equals-univ + even-via-2m.
- **Difficulty**: standard. Estimated ~10 LoC.

### T4 (all pairs commute)

Combines T1, T2, T3 via `CSSCommutationLemmas.ZType_commutes` and
`XType_commutes`. Two-way `rcases` on Z-vs-X membership; 4 cases (2
trivial diag from CSS, 2 cross from T3 + symmetry).

- **Difficulty**: trivial after T1/T2/T3.

### T5 (`−I ∉ subgroup`)

Standard CSS argument via `CSS.negIdentity_not_mem_closure_union`.

- **Difficulty**: trivial.

### T6 (`listToSet_generatorsList`)

```lean
def generatorsList (m : ℕ) [Fact (2 ≤ m)] : List (NQubitPauliGroupElement (2 * m)) :=
  [S_Z m, S_X m]

lemma listToSet_generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    listToSet (generatorsList m) = generators m := by
  simp only [generatorsList, generators, ZGenerators, XGenerators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g; simp only [...]
```

Same pattern as `FourQubit_4_2_2.lean` (which has `[Z1, X1]`).

- **Difficulty**: trivial.

### T7 (`AllPhaseZero`)

Same pattern as `FourQubit_4_2_2.lean`. Both generators have `phasePower = 0`
by construction.

- **Difficulty**: trivial.

### T8 (Generator independence — PARAMETRIC, this is the main risk)

The check matrix of `[S_Z m, S_X m]` is the `2 × 4m` matrix

```
S_Z m | 0 0 ... 0 | 1 1 ... 1
S_X m | 1 1 ... 1 | 0 0 ... 0
```

We need linear independence of these two rows over `ZMod 2`. Two
nontrivial linear combinations: each row alone (already nonzero), and
their sum `1 1 ... 1 1 1 ... 1` (also nonzero). The 4 combinations are:
{0, row₁, row₂, row₁+row₂}, three nonzero.

**Proof approach**: `rowsLinearIndependent` unfolds to "for all `f : Fin 2 →
ZMod 2`, `(∀ j, ∑ i, f i * checkMatrix i j = 0) → f = 0`". For our
two-row case, the columns split as:

- **Columns 0 to 2m−1 (X-part)**: only row 2 (`S_X`) contributes, so the
  per-column constraint is `f 1 * 1 = 0`, forcing `f 1 = 0`.
- **Columns 2m to 4m−1 (Z-part)**: only row 1 (`S_Z`) contributes, so the
  per-column constraint is `f 0 * 1 = 0`, forcing `f 0 = 0`.

So both coefficients must vanish — independence holds. Implementation:

```lean
theorem rowsLinearIndependent_generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList m) := by
  unfold NQubitPauliGroupElement.rowsLinearIndependent
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  -- Specialize hf at an X-column (e.g. Fin.castAdd m 0) to get f 1 = 0
  -- Specialize hf at a Z-column (e.g. Fin.natAdd (2*m) 0) to get f 0 = 0
  -- Then fin_cases i; assumption / exact h_X / exact h_Z
  sorry
```

Could possibly be closed by `decide` if we manage to specialize to a
concrete `m` first, but since `m` is symbolic, we need a parametric
argument. Estimated effort: ~30–50 LoC (the more complex parametric
proof in the file).

- **Approach**: hand-rolled per-column specialization (no induction needed
  because there are only 2 rows).
- **Difficulty**: standard. The parametric flavor is the only friction;
  the actual math is simpler than `RepetitionCode/N.lean`'s 3-band
  argument.
- **Risk**: needs `Fin.natAdd` / `Fin.castAdd` discipline for indexing.

### T9, T10 (StabilizerGroup packaging)

Standard `mkStabilizerFromGenerators` invocation. Mirror
`RepetitionCodeN.lean:388–395`.

- **Difficulty**: trivial.

### T11 (logical X anticomm logical Z, diagonal)

For each `i : Fin (2m − 2)`:

```lean
theorem logicalX_anticommutes_logicalZ_diag (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    Anticommute (logicalX m i) (logicalZ m i) := by
  classical
  pauli_anticomm_odd_anticommutes
  -- Goal: Odd ((Finset.univ.filter (anticommutesAt ...)).card)
  -- Show filter = {⟨i.val, by omega⟩} (the qubit-i index lifted into Fin (2m))
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (logicalX m i).operators (logicalZ m i).operators)) =
        ({⟨i.val, by omega⟩} : Finset (Fin (2 * m))) := by
    ext j
    -- Per-qubit analysis: anticommute at qubit j iff j = i-as-Fin(2m)
    -- Three positions matter:
    --   - j = i (lifted): X vs Z, anticommute
    --   - j = 2m-1: X vs I, commute
    --   - j = 2m-2: I vs Z, commute
    --   - else: I vs I, commute
    sorry
  rw [hfilter, Finset.card_singleton]; decide
```

The `hfilter` proof is the parametric meat. Need to do per-qubit case
analysis without `fin_cases` (since `m` is symbolic). The approach is
`by_cases` on the three "interesting" positions plus the general case,
using `Fin.ext_iff` to compare values numerically.

- **Approach**: 4-case `by_cases` on the qubit's value being `i`, `2m-2`,
  `2m-1`, or "other".
- **Difficulty**: standard parametric (~25 LoC per logical (anti)comm).
  This proof shape appears 6 times (T11, T12c, T13×2 directions, T14×2),
  so a private helper `pauli_overlap_at_pair_set` would amortize.
- **Risk**: `Fin.ext` reasoning on `2m - 1` and `2m - 2` can trip up
  `simp`. Workaround: `omega` after `Fin.ext_iff`.

### T12 (logical pairwise commutation)

- **T12a (X̄_i · X̄_j)**: both X-type, use `XType_commutes` /
  `pauli_comm_componentwise`. Trivial.
- **T12b (Z̄_i · Z̄_j)**: dual of T12a. Trivial.
- **T12c (X̄_i · Z̄_j for i ≠ j)**: anticomm support is empty, so commute.
  Proof: filter equals `∅`, cardinality 0, even.

  The subtlety: we need `i ≠ j ⇒ (i : Fin (2m)) ≠ (j : Fin (2m))` (when
  lifting `Fin (2m−2) ↪ Fin (2m)`). This follows from the lift being
  injective — write the lift as `Fin.castLE` (with the bound proof) and
  use `Fin.castLE_injective`.

  ```lean
  theorem logicalX_commutes_logicalZ_offdiag (m : ℕ) [Fact (2 ≤ m)]
      {i j : Fin (2 * m - 2)} (hij : i ≠ j) :
      logicalX m i * logicalZ m j = logicalZ m j * logicalX m i := by
    classical
    pauli_comm_even_anticommutes
    have hfilter : (Finset.univ.filter
        (anticommutesAt (logicalX m i).operators (logicalZ m j).operators))
        = (∅ : Finset (Fin (2 * m))) := by
      ext k; simp [Finset.mem_filter, anticommutesAt, logicalX, logicalZ, ...]
      -- Per-qubit case analysis: no anticomm at any qubit because supports
      -- are disjoint when i ≠ j (and i, j < 2m-2).
      sorry
    rw [hfilter, Finset.card_empty]
    exact even_zero
  ```

- **Difficulty**: T12a/b trivial, T12c standard parametric (similar shape
  to T11 but with empty filter).

### T13, T14 (logicals in centralizer)

Standard pattern from `FourQubit_4_2_2.lean:384`: rewrite via
`StabilizerGroup.mem_centralizer_iff_closure`, intro `s ∈ generators`,
case-split on Z- or X-gen, dispatch via per-generator commutation lemma.

The per-generator commutation lemmas are:

- `logicalX_commutes_S_Z m i`: `logicalX m i * S_Z m = S_Z m * logicalX m i`.
  Anticomm support `{i, 2m-1}`, count 2, even ⇒ commute. (Parametric.)
- `logicalX_commutes_S_X m i`: `logicalX m i * S_X m = S_X m * logicalX m i`.
  Both X-type, trivial via `XType_commutes`.
- `logicalZ_commutes_S_Z m i`: both Z-type, trivial.
- `logicalZ_commutes_S_X m i`: anticomm support `{i, 2m-2}`, count 2, even ⇒
  commute. (Parametric.)

- **Difficulty**: parametric but mechanical (~15 LoC × 2 each).

### T15 (StabilizerCode packaging — the k = 2m-2 novelty)

The `logical_commute_cross` field requires a `fin_cases ℓ <;> fin_cases ℓ'`
expansion. **Cannot literally `fin_cases` over `Fin (2m − 2)` because `m` is
symbolic.** Instead, use `if hℓ : ℓ = ℓ' then exact (hne hℓ).elim else
[per-case commutations]`. The per-case commutations (T12a, T12b, T12c, and
T12c flipped) are then applied unconditionally — they don't depend on
specific `ℓ, ℓ'` values, only on `ℓ ≠ ℓ'`.

```lean
private def logicalOpsIceberg (m : ℕ) [Fact (2 ≤ m)] :
    Fin (2 * m - 2) → LogicalQubitOps (2 * m) (stabilizerGroup m) :=
  fun i => ⟨logicalX m i, logicalZ m i,
            logicalX_mem_centralizer m i, logicalZ_mem_centralizer m i,
            logicalX_anticommutes_logicalZ_diag m i⟩

noncomputable def stabilizerCode (m : ℕ) [Fact (2 ≤ m)] :
    StabilizerCode (2 * m) (2 * m - 2) where
  hk := by have : Fact (2 ≤ m) := inferInstance; omega
  -- (... usual fields with parametric proofs from T6-T14 ...)
  logicalOps := logicalOpsIceberg m
  logical_commute_cross := fun ℓ ℓ' hne => by
    -- Cannot fin_cases on Fin (2m - 2) symbolically.
    -- Instead, apply T12 unconditionally.
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact logicalX_commutes_logicalX m ℓ ℓ'  -- T12a (always commutes)
    · exact logicalX_commutes_logicalZ_offdiag m hne  -- T12c (i ≠ j)
    · exact (logicalX_commutes_logicalZ_offdiag m (Ne.symm hne)).symm  -- T12c flipped
    · exact logicalZ_commutes_logicalZ m ℓ ℓ'  -- T12b (always commutes)
```

- **Difficulty**: standard once T11-T14 are in place. The `fin_cases`
  problem is sidestepped by stating T12a/b as "for all i j" (no `i ≠ j`
  hypothesis), and T12c as "for `i ≠ j`" (with the `hne` hypothesis).
  See "Risk register" below for an alternative.

### T16 (stabilizerCode_toSubgroup_eq)

Trivial `change` + `rw [listToSet_generatorsList]`. Mirror
`FourQubit_4_2_2.lean:472`.

### T17 (weight-1 anti-witness — parametric)

```lean
private lemma weight_one_anticomm_witness (m : ℕ) [Fact (2 ≤ m)] :
    ∀ i : Fin (2 * m), ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators m, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  match P, hP with
  | PauliOperator.X, _ =>
    exact ⟨S_Z m, by simp [generators, ZGenerators],
      weightOneAt_X_anticomm_S_Z m i⟩
  | PauliOperator.Y, _ =>
    exact ⟨S_Z m, by simp [generators, ZGenerators],
      weightOneAt_Y_anticomm_S_Z m i⟩
  | PauliOperator.Z, _ =>
    exact ⟨S_X m, by simp [generators, XGenerators],
      weightOneAt_Z_anticomm_S_X m i⟩
  | PauliOperator.I, hP => exact (hP rfl).elim
```

with three private helpers:

- `weightOneAt_X_anticomm_S_Z m i`: weight-1 X at qubit `i` vs. all-Z S_Z.
  Anticomm support is `{i}` (X·Z anticommute at qubit i; everywhere else
  the weight-1 element has I, commute). Single qubit, odd ⇒ anticommute.
- `weightOneAt_Y_anticomm_S_Z m i`: weight-1 Y at qubit `i` vs. all-Z S_Z.
  Same structure (Y·Z anticommute).
- `weightOneAt_Z_anticomm_S_X m i`: weight-1 Z at qubit `i` vs. all-X S_X.
  Symmetric.

Each is the **parametric version** of `FourQubit_4_2_2.lean`'s
`weightOneAt_anticomm_Z1` (lines 480–495). The proof shape is identical;
the only change is the filter equality, which needs a per-qubit
`by_cases j = i` instead of `fin_cases j` (since `m` symbolic).

- **Difficulty**: standard parametric (~15 LoC each, 3 helpers).
- **No `hi_dichotomy` needed** (cleaner than `CSS_4_1_2.lean`).

### T18 (HasCodeDistance 2 — one-liner via PR #34 helper)

```lean
theorem code_has_distance_two (m : ℕ) [Fact (2 ≤ m)] :
    HasCodeDistance (stabilizerCode m) 2 :=
  hasCodeDistance_two_of_anticommute_witness (stabilizerCode m)
    (generators m)
    (stabilizerCode_toSubgroup_eq m)
    (weight_one_anticomm_witness m)
    ⟨logicalX m ⟨0, by have : Fact (2 ≤ m) := inferInstance; omega⟩,
      (logicalOpsIceberg m _).xOp_nontrivial,
      ?_⟩
```

The `?_` is `weight (logicalX m ⟨0, _⟩) = 2`. This is **parametric weight
2** (not `decide`-able for symbolic `m`). Need a `weight_logicalX` lemma.

- **Difficulty**: standard once the weight-2 helper is in place.
  Estimated 10 LoC for the helper, 5 LoC for the use.
- **Risk**: parametric weight computation may be fiddly; see
  `gap_audit.md`.

### T19 (StabilizerCodeWithDistance packaging)

Trivial wrapper.

## Risk register

1. **Parametric weight computation (T18 witness).** For symbolic `m`, the
   weight of `logicalX m 0` (X at two qubits, identity elsewhere) equals
   2. Need a `weight_setIdentity_set_set` style lemma or a direct
   computation. Likely candidate: `NQubitPauliOperator.weight_set_set`
   showing `weight ((identity n).set i P |>.set j Q) = (1 if P ≠ I else 0) + (1 if Q ≠ I else 0)` when
   `i ≠ j`. May not exist yet; if not, write the proof inline.

2. **`Fin (2m - 2)` lift to `Fin (2m)`.** Need a clean coercion. Two
   approaches:
   - `Fin.castLE (Nat.sub_le _ _)` — works for `2m - 2 ≤ 2m`.
   - `⟨i.val, by omega⟩` — explicit construction.

   Either is fine; the second is more explicit and grep-able.

3. **`Fin (2 * m - 2)` itself is awkward.** Lean's `Fin (2 * m - 2)` works
   fine when `m ≥ 2`, but `Fin.cases` / `fin_cases` won't reduce
   symbolically. **All proofs over this index must avoid `fin_cases`** —
   instead, use `Fin.ext_iff` to compare `Fin` values numerically and
   `omega` to discharge bounds. This is the same discipline as
   `RotatedSurfaceCodeN.lean` and `RepetitionCode/N.lean`.

4. **`logical_commute_cross` field with parametric `Fin k`.** Cannot
   `fin_cases ℓ`, so the proof has to work by structure. Mitigation
   strategy: state T12a and T12b "always commute" (no `i ≠ j` hypothesis,
   trivially derived from X-type / Z-type structure), state T12c "for
   `i ≠ j`" (with the `hne` carry). Then the `logical_commute_cross` field
   is just `refine ⟨T12a, T12c, T12c.symm, T12b⟩`.

5. **Independence parametric proof (T8).** This is the longest part of the
   file. Mitigation: it's structurally simpler than `RepetitionCode/N.lean`
   because there are only 2 rows; the per-column specialization is direct.

6. **Module orphan trap.** Need to add `Iceberg.lean` umbrella and import
   from `Codes.lean`. Both edits required; without them the file would
   silently never be compiled.

7. **Stage-3 SKIPPED.** Per the task spec: "The user is running this
   end-to-end without human review. Your `informal_spec.md` MUST be
   self-sufficient." The above logical-operator convention has been
   verified by hand (see informal_spec.md § "By-hand verification of the
   (anti)commutation table") and cross-checked against the m = 2
   specialization. The papers do not specify a canonical logical basis
   (verified by direct WebFetch); the choice is documented as a deliberate
   convention with full justification.

## Estimated effort

- LoC: **~500** total (matches the scoring estimate). Breakdown:
  - Imports + header: 30
  - Generators + sets (§1–§2): 30
  - Type predicates (§3, T1–T2): 30
  - Cross-commutation (§4, T3): 25
  - All-pair commutation (§5, T4): 20
  - −I lemma (§6, T5): 10
  - Generator list + phase 0 (§7, T6, T7): 30
  - Independence (§9, T8): **50** (main parametric proof; biggest risk)
  - StabilizerGroup (§8, T9, T10): 25
  - Logical operators (§10): 25
  - Logical anticommutation (§11, T11, T12): **80** (k = 2m-2 family, 4 cases)
  - Logical centralizer (§12, T13, T14): **80** (per-generator commutation, 4 helpers)
  - StabilizerCode packaging (§13, T15): 50
  - Distance bridge + witness (§14, T16, T17): 40
  - HasCodeDistance + packaging (T18, T19): 15
- Time: **2 sessions** (one to close T1–T10, one for T11–T19).
- Proof attempts: the longest is T8 (independence) at ~30–50 LoC.

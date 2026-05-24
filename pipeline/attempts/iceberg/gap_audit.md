# Gap audit: iceberg `[[2m, 2m−2, 2]]`

## Repo gaps (this code surfaces / requires new abstractions)

### Gap 1: parametric "all-X commutes with all-Z when `n` is even" lemma

**Status: missing in `Foundations/BinarySymplectic/SymplecticInner.lean`.**

The current `allX_allZ_anticommute (n : ℕ) (hn : Odd n)` lemma
(SymplecticInner.lean:106) gives the **odd `n`** anticommute fact. The dual
"**even `n` ⇒ commute**" is needed for T3 (the iceberg stabilizer's whole
existence depends on this fact: `S_X · S_Z = S_Z · S_X` precisely because
`n = 2m` is even). It does not appear to exist anywhere in
`Foundations/`.

**Resolution path during Stage 4:**

- **Option A (preferred)**: prove the commutation inline in the iceberg
  file using `pauli_comm_even_anticommutes` + filter-equals-univ + the
  parametric evenness fact `Even (2 * m)`. The proof is ~10 LoC.
- **Option B (cleanup PR after iceberg lands)**: add a dual
  `allX_allZ_commute_of_even (n : ℕ) (hn : Even n) : (⟨0, X n⟩ : ...) *
  (⟨0, Z n⟩ : ...) = (⟨0, Z n⟩ : ...) * (⟨0, X n⟩ : ...)` lemma to
  `SymplecticInner.lean`. Then the iceberg's T3 becomes one line:
  `allX_allZ_commute_of_even (2 * m) (by ⟨m, by ring⟩)`.

**Recommend Option A** for the initial PR (keeps the iceberg PR focused).

### Gap 2: parametric weight-of-weight-2-Pauli lemma

**Status: probably missing.**

T18 needs `weight (logicalX m 0) = 2` for symbolic `m`. The logical X is
`((identity (2m)).set i X).set j X` with `i ≠ j` (here `i = 0` and
`j = 2m - 1`). There may or may not be a generic
`weight_set_set_of_ne_of_both_nonI` helper; needs investigation during
Stage 4.

**Possible candidate names to grep for first:**
- `weight_set`
- `weight_setIdentity`
- `weight_of_support`
- `NQubitPauliOperator.weight`

**Resolution path:**
- If a helper exists, use it directly.
- If not, prove the weight inline by directly computing the support
  cardinality:
  ```lean
  have hsupp : (logicalX m 0).operators.support = {⟨0, _⟩, ⟨2*m - 1, _⟩} := by
    ext k; ... -- 4-case by_cases on k
  have : weight (logicalX m 0) = 2 := by
    rw [weight, NQubitPauliOperator.weight_eq_support_card, hsupp,
      Finset.card_insert_of_notMem (by ...), Finset.card_singleton]
  ```
  Cost: ~10 LoC.

### Gap 3: `Fin (2 * m - 2) ↪ Fin (2 * m)` coercion clarity

**Status: no clean reusable helper; explicit construction needed.**

The lift `i : Fin (2m - 2)` to `Fin (2m)` is needed many times throughout
the file (definition of `logicalX`, definition of `logicalZ`, every
commutation-filter proof). `Fin.castLE` would work but requires the bound
proof `2*m - 2 ≤ 2*m` to be passed each time. An anonymous constructor
`⟨i.val, by ...⟩` keeps the call sites short but obscures structure.

**Decision**: use a private abbreviation early in the file:

```lean
/-- Lift a logical-qubit index `Fin (2m-2)` into the physical-qubit index
`Fin (2m)`. -/
@[inline] private def logIdx {m : ℕ} [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    Fin (2 * m) :=
  ⟨i.val, by have : Fact (2 ≤ m) := inferInstance; omega⟩
```

This keeps each call site to `logIdx i` instead of either repeating the
bound proof or invoking `Fin.castLE` with the bound proof as argument.

**Note**: this is an idiom, not a repo-wide gap — but worth flagging in
case a similar pattern is later promoted to `Geometry/`.

### Gap 4: parametric `fin_cases` for `Fin (2 * m - 2)`

**Status: known limitation, no resolution needed.**

`fin_cases ℓ` does not work on `Fin (2 * m - 2)` when `m` is symbolic.
This affects T15's `logical_commute_cross` field: rather than the
`fin_cases ℓ <;> fin_cases ℓ' <;> exact ...` pattern from
`FourQubit_4_2_2.lean:459`, we use a structural `refine ⟨_, _, _, _⟩`
that consumes the always-commute T12a/T12b lemmas and the conditional
T12c lemma. Same trick used in `RepetitionCodeN.lean:443`
(`logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim`)
— but that proof requires `Subsingleton (Fin k)` which only holds for
`k ≤ 1`. The iceberg's `k = 2m - 2 ≥ 2` violates that.

**Resolution**: spelled out in `plan.md` § T15. No new abstraction needed.

## Mathlib gaps (lemmas not in mathlib v4.30)

None expected. The parametric proofs use only:

- `Finset.univ.filter`, `Finset.card`, `Finset.card_singleton`,
  `Finset.card_empty`, `Finset.card_insert_of_notMem`, etc.
  — all standard.
- `Even`, `Nat.even_two_mul`, `even_two`, `Even.zero` — standard.
- `Fin.val_eq_val`, `Fin.ext`, `Fin.castLE` — standard.
- `Nat.sub` arithmetic via `omega` — standard.
- `simp +decide`, `pauli_comm_even_anticommutes` — repo-local.

No new mathlib lemma is required.

## Likely "BLOCKED(<reason>)" sorries

**None anticipated.** All theorems should close with current infrastructure
+ the inline-proven parametric lemmas in the iceberg file. The risks are
about LoC budget and proof-engineering effort, not about missing
abstractions.

If something unexpected blocks Stage 4 — e.g., the `pauli_comm_even_anticommutes`
tactic fails to specialize to `Fin (2 * m)` — the fallback is to prove the
commutation directly via `NQubitPauliGroupElement.commutes_iff_symplectic_inner_zero`
plus a hand computation. This is still a "no blocker" path; just more LoC.

## Architectural / future-cleanup notes

1. **Move `allX_allZ_commute_of_even` to `SymplecticInner.lean`** in a
   follow-up PR (per Gap 1, Option B).

2. **Move `Fin (2m-2) ↪ Fin (2m)` lift to `Geometry/FinPeriodic.lean`** if
   subsequent parametric codes need similar lifts. Currently it's
   iceberg-specific; promote if a second use site appears.

3. **Generalize `hasCodeDistance_two_of_anticommute_witness` to
   `hasCodeDistance_d_of_anticommute_witnesses_le_d_minus_one`** in a
   future PR — for distance-3+ codes the helper currently only handles
   `d = 2`. This is out of scope for iceberg (it's a `d = 2` code), but
   noting for the next non-CSS code in the queue.

4. **`pauli_comm_componentwise` extension**: the current tactic handles
   componentwise commutation when supports are disjoint or identical. For
   the off-diagonal logical commutation T12c (where `X̄_i` and `Z̄_j` have
   disjoint supports when `i ≠ j`), this tactic might already close the
   goal in one line — investigate during Stage 4. If yes, T12c shrinks
   from ~25 LoC to 1 line.

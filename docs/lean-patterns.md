# Lean tactic patterns by code shape

Reference manual of tactical patterns useful when formalizing specific
kinds of QEC codes in this repo. Each pattern has a canonical use site so
you can see it in context.

**Add patterns here**, not to `CLAUDE.md`, when:
- the pattern is specific to a code shape (CSS distance, non-CSS, parametric, etc.)
- it's a mechanical fix for a recurring gotcha
- it's a workaround for a Lean / mathlib quirk that isn't strictly
  version-specific (those go in `mathlib-version-quirks.md`)

`CLAUDE.md` is the small "must-read on every invocation" doc. This file
is the reference you reach for when your current code matches one of the
sections below.

## Index

- [CSS distance proofs](#css-distance-proofs)
- [Non-CSS distance proofs](#non-css-distance-proofs)
- [Parametric code families](#parametric-code-families)
- [Fast kernel `decide` for big finite walks](#fast-kernel-decide-for-big-finite-walks)
- [Mechanical fixes for common gotchas](#mechanical-fixes-for-common-gotchas)

---

## CSS distance proofs

### Distance-2 packaging via `hasCodeDistance_two_of_anticommute_witness`

Single closer for "distance is exactly 2" given (a) a weight-1 anticommute
witness function and (b) an explicit weight-2 nontrivial logical. Defined
in `Framework/Core/CSS/CSSDistance.lean`; canonical signature:

```lean
theorem hasCodeDistance_two_of_anticommute_witness {k : ℕ} (C : StabilizerCode n k)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : C.toStabilizerGroup.toSubgroup = Subgroup.closure genSet)
    (h_anticomm : ∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
      ∃ g ∈ genSet, Anticommute (weightOneAt i P) g)
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = 2) :
    HasCodeDistance C 2
```

Replaces the 8-line `refine hasCodeDistance_of … ⟨…⟩ ?_ ; intro …;
interval_cases w; rcases (IsNontrivialLogicalOperator_iff …).mp …; exact …`
boilerplate. Use sites: `Codes/Small/FourQubit_4_2_2.lean`,
`Codes/Small/CSS_4_1_2.lean`, `Codes/Iceberg/N.lean` (T18 in each).

### Multiple Z-generators (or X-generators) covering disjoint qubit subsets

When a CSS code has multiple Z-stabilizers whose supports partition (or
sub-partition) the qubits, factor the "which generator covers `i`"
dichotomy out once and reuse across the `P = X` and `P = Y` match arms
rather than re-doing `by_cases` in each:

```lean
have hi_dichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) := by
  fin_cases i <;> tauto
```

In each per-generator filter-equality helper, dispatch `rcases hi <;>
rcases hP` *inside* the `ext` proof before `fin_cases j` — keeps the
helper universally quantified over `i` instead of forcing per-case
specializations:

```lean
have hfilter :
    (Finset.univ.filter (anticommutesAt (weightOneAt i P) S_Z1)) =
      ({i} : Finset (Fin 4)) := by
  ext j; rcases hi with rfl | rfl <;> rcases hP with rfl | rfl <;>
    fin_cases j <;> simp [...]
```

Canonical use site: `CSS_4_1_2.lean`'s `weight_one_anticomm_witness` (T19).

### Multiple Z-generators (or X-generators) with **overlapping** qubit supports

When the Z-stabilizer supports do *not* partition the qubits — they overlap
on some shared subset — the `hi_dichotomy` pattern above extends to a
**trichotomy**: one branch for the shared region (where either Z-stab works
as the witness), plus one branch for each "private" region.

Canonical use site: `SixQubit_6_2_2.lean`'s `weight_one_anticomm_witness`
(T31). The Knill C_6 Z-stabilizers `S_Z1 = ZZZZII` (qubits {0,1,2,3}) and
`S_Z2 = ZZIIZZ` (qubits {0,1,4,5}) **overlap at {0,1}**, so:

```lean
have hi_trichotomy :
    (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5) := by
  fin_cases i <;> tauto
```

Within the shared region, **pick one Z-stab consistently** (e.g. always
use `S_Z1` when `i ∈ {0, 1}`) so downstream proofs of
`weight_one_anticomm_witness` aren't case-fragile. The trichotomy lifts to
the broader disjunction the per-generator helpers take via
`rcases hi with rfl | rfl <;> tauto`.

### Multi-logical-qubit (`k ≥ 2`) `logical_commute_cross` dispatch

For the `logical_commute_cross` field of `StabilizerCode n k` when `Fin k`
is **concrete** (e.g. `Fin 2` for `k = 2`), the natural dispatch is
`fin_cases ℓ <;> fin_cases ℓ'`, which produces `k²` cases per direction
(4 for `k = 2`). The standard arrangement:

```lean
refine ⟨?_, ?_, ?_, ?_⟩
· -- ∀ ℓ ℓ', X̄_ℓ * X̄_ℓ' = X̄_ℓ' * X̄_ℓ  (both X-type, all 4 cases)
  intro ℓ ℓ'; fin_cases ℓ <;> fin_cases ℓ' <;>
    first | rfl | exact X1X2_comm | exact X1X2_comm.symm
· -- analogous for both Z-type
· -- ∀ ℓ ℓ', ℓ ≠ ℓ' → X̄_ℓ * Z̄_ℓ' = Z̄_ℓ' * X̄_ℓ  (diagonal cases discharged)
  intro ℓ ℓ' hℓℓ'; fin_cases ℓ <;> fin_cases ℓ' <;>
    first | exact (hℓℓ' rfl).elim | exact X1Z2_comm | exact X2Z1_comm.symm
· -- analogous for Z̄_ℓ * X̄_ℓ'
```

The `.symm` arrangement is needed for the `(ℓ', ℓ)` direction (where the
previously-proved lemma was stated in the other order). The
`(hℓℓ' rfl).elim` disposes of the `ℓ = ℓ'` diagonal cases for cross-type
commutation. Canonical use sites: `FourQubit_4_2_2.lean` (first k=2
instance) and `SixQubit_6_2_2.lean` (second).

For **parametric** `Fin k` where `fin_cases` doesn't work, see
"Bypassing `fin_cases ℓ <;> fin_cases ℓ'` for parametric `Fin n`" under
§ Parametric code families — `Iceberg/N.lean` uses a structural-refine
workaround instead.

### `pauli_comm_componentwise` handles disjoint-support mixed-type cases

When two Pauli operators have *disjoint* supports (no qubit where both
are non-I), their product commutes for free via
`pauli_comm_componentwise` — no need for `pauli_comm_even_anticommutes`
or filter-cardinality arguments, even when one is X-type and the other
is Z-type. The `gap_audit.md` for `SixQubit_6_2_2` flagged this as a
risk for T18 (`logicalX_1` at {2,3} vs `logicalZ_2` at {4,5}, mixed
types but disjoint); it didn't materialize. Closing tactic was a
one-line `pauli_comm_componentwise`. Don't reach for the parity-based
helpers when supports don't overlap.

### Anti-witness function when all generators have full support

The counter-pattern to the multi-Z dichotomy above. When the all-X
stabilizer covers every qubit AND the all-Z stabilizer covers every qubit
(e.g. iceberg's `S_X m = XX…X`, `S_Z m = ZZ…Z`), **no `hi_dichotomy`
is needed**. A plain 3-way `match P, hP` over `{X, Y, Z}` suffices —
each branch picks the unique generator that anticommutes with `P` at
qubit `i`:

```lean
intro i P hP
match P, hP with
| PauliOperator.X, _ => exact ⟨S_Z m, by simp [generators, ZGenerators], …⟩
| PauliOperator.Y, _ => exact ⟨S_Z m, by simp [generators, ZGenerators], …⟩
| PauliOperator.Z, _ => exact ⟨S_X m, by simp [generators, XGenerators], …⟩
| PauliOperator.I, hP => exact (hP rfl).elim
```

Canonical use site: `Iceberg/N.lean`'s `weight_one_anticomm_witness` (T17).
If you find yourself reaching for `hi_dichotomy` on a CSS code with
full-support stabilizers, you're overcomplicating it.

### `NQubitPauliOperator.identity` in simp sets for CSS generator equality

For CSS generator-equality lemmas (e.g., `ZGenerators_are_ZType`,
`XGenerators_are_XType`), drop `identity` from the simp set when a
generator's `.set` chain *fully covers* every `Fin n` position (e.g.
`S_X1 = ...set 0 X.set 1 X.set 2 X.set 3 X` on `Fin 4`). Keep
`identity` for partial-coverage generators (e.g.
`S_Z1 = ...set 0 Z.set 1 Z` on `Fin 4` — qubits 2 and 3 fall through to
`identity`). `linter.unusedSimpArgs` flags the wrong choice. First hit:
`CSS_4_1_2.lean`'s T1 (`ZGenerators_are_ZType`) vs. T2
(`XGenerators_are_XType`).

---

## Non-CSS distance proofs

### `Anticommute p q` via `by decide`

A computable `DecidableEq (NQubitPauliGroupElement n)` and a
`noncomputable` `Decidable Anticommute` instance let `decide` reduce
`Anticommute p q` for concrete Pauli group elements. **`native_decide`
does NOT work** here (because `Mul` on `NQubitPauliGroupElement` is
`noncomputable`) — prefer `decide`.

These instances live as `local instance` in
`Codes/FiveQubit_5_1_3.lean` to avoid global synthesis pollution (see
the global-vs-local discipline bullet in `CLAUDE.md`); copy them into
any new non-CSS code file that needs them.

### Backtracking witness search

When proving "for every weight-`k` Pauli, some generator anticommutes",
the standard pattern is:

```lean
fin_cases i <;>
  (match P, hP with
   | .X, _ => first
     | exact ⟨g₁, by simp [generators], by decide⟩
     | exact ⟨g₂, by simp [generators], by decide⟩
     | …
   | .Y, _ => …
   | .I, hP => exact (hP rfl).elim)
```

`first` backtracks across generators by `decide`. Trim unused generator
branches per `(P, …)` case (flagged by `linter.unusedTactic`) to keep
the file lint-clean. See `FiveQubit_5_1_3.lean`'s
`weight_one_anticomm_witness` and `weight_two_anticomm_witness` for
canonical use sites.

---

## Parametric code families

These patterns are specific to parametric formalizations (`Iceberg/N.lean`,
`RotatedSurface/N.lean`, `Toric/CodeN.lean`, `Repetition/N.lean`). Most
break when `Fin n` has parametric `n`.

### Parametric column-evaluation for `rowsLinearIndependent`

When the check-matrix dimension is parametric, the `by decide` approach
used for concrete-`n` codes fails. The clean parametric pattern is to
peel off each row of `f` by evaluating `hf` at carefully chosen columns:

```lean
-- T8 in Iceberg/N.lean:
intro f hf
have h0 : f 0 = 0 := by
  have := congrFun hf (Sum.inl 0)  -- evaluate at the first Z-column
  -- the row-sum reduces to f 0 * 1 + f 1 * 0 = f 0
  simpa [...] using this
have h1 : f 1 = 0 := by
  have := congrFun hf (Sum.inr 0)  -- evaluate at the first X-column
  simpa [...] using this
ext i; fin_cases i <;> [exact h0; exact h1]
```

Generalizes to any small CSS code where the natural check matrix has
"single-block" rows (a Z-row covering some columns + an X-row covering
the complementary columns).

### Bypassing `fin_cases ℓ <;> fin_cases ℓ'` for parametric `Fin n`

The `pauli_comm_componentwise` tactic and the `logical_commute_cross`
field of `StabilizerCode` both want to enumerate over `Fin (n - k)`,
which `fin_cases` can't do when `n - k` is parametric. The workaround
is to *structurally* decompose `∀ ℓ ℓ', …` via `refine ⟨_, _, _, _⟩`
into the `i = j` and `i ≠ j` sub-cases, then dispatch each case to a
previously-proved lemma:

```lean
refine ⟨?_, ?_, ?_, ?_⟩
· intro ℓ ℓ'; exact logicalX_commutes_logicalX m ℓ ℓ'        -- both X-type
· intro ℓ ℓ'; exact logicalZ_commutes_logicalZ m ℓ ℓ'        -- both Z-type
· intro ℓ ℓ' hℓℓ'                                            -- cross, i ≠ j
  by_cases hij : ℓ = ℓ'
  · exact absurd hij hℓℓ'
  · exact logicalX_commutes_logicalZ_offdiag m ℓ ℓ' hij
· …
```

Canonical use site: `Iceberg/N.lean` (T15 = `stabilizerCode` structure
literal).

### `simp [foo]` → `simp only [foo]` for `@[inline] private def`

When the `simp` is just unfolding an `@[inline] private def`, replace
with `simp only [foo]`. The narrower form satisfies `linter.flexible`
and (with `@[inline]`) reduces identically. Canonical hit:
`Iceberg/N.lean`'s `logIdx_ne_xAnchor` lemma uses `simp only [logIdx]`
not `simp [logIdx]`.

---

## Fast kernel `decide` for big finite walks

Trigger: an axiom-clean enumeration (`by decide` over `4⁶`-ish cases) takes
minutes-to-tens-of-minutes and/or needs a `maxHeartbeats` bump. Seen on the BB
slot-frame walks (`WtFloor24Bridge.RBlock_std_ge6` was ~24 min of the Jul 2026
BB build; ~0.5 s after this treatment).

Three independent levers, in order of leverage:

1. **Pack lookup tables into `Nat` literals.** `Array Nat` literals reduce in
   the kernel as *linked-list walks* — `Array.getD` on a 512-entry table costs
   ~hundreds of recursor steps per lookup. Pack the table into one `Nat`
   (k bits per entry) and index with `(TBL >>> (k*i)) &&& mask`:
   `Nat.shiftRight`/`Nat.land`/`Nat.mod` are GMP-accelerated in the kernel, so
   a lookup is ~2 ops. Keep the readable `Array` next to it and certify
   agreement with a 1-line kernel `decide` (see `WtFloor24.slotCost_eq_table`).
   **Watch the `getD` default**: if the index range exceeds the array length,
   the packed literal must reproduce the default at the out-of-range slots
   (`MImClassify.WT5_N` pads indices 512–513 with `99`, 8 bits per entry).
2. **Replace `Matrix.of ![![…]]` op tables with `Nat` ops.** `![…] a b`
   reduces through `Fin.cases` chains. If the op has closed form, use it
   (`CRTFrame.fadd` is XOR: `⟨(a.val ^^^ b.val) % 4, by omega⟩`); otherwise
   pack the table as in (1) (`CRTFrame.fmul`, 2 bits/entry). The `% 4` keeps
   the `Fin.mk` bound `omega`-provable (omega can't see `^^^`/`&&&`).
3. **`decide +kernel`.** Plain `decide` evaluates the instance *twice* — once
   in the elaborator (slow, allocation-heavy; the multi-GB RSS spikes) and
   once in the kernel. `+kernel` skips the elaborator pass entirely, which
   also frees the declaration from `maxHeartbeats` (kernel checking is not
   heartbeat-metered) — the bump and its mandatory comment can be dropped.

Measured on `RBlock_std_ge6` (4096 cases × 12 table lookups + 36 F₄ ops):
plain `decide` ≈ 15–20 min / ~6 GB; `decide +kernel` alone ≈ 232 s / 6 GB;
levers 1+2+3 together ≈ 0.4 s / negligible.

Related native-side batching: N separate `native_decide` calls in one file pay
N C-compile round-trips (~2–4 s each). Bundle them into a single `∧`-chain
theorem proved by one `native_decide` and destructure (`MImAssembly.transfer_covs`,
63→1; `MImFloorY11.offs_eq`, 24→1).

**`native_decide` is interpreted, not compiled.** At elaboration time
`native_decide` evaluates through Lean's IR interpreter (only stdlib calls in
`libleanshared` run truly native), so every boxed apply costs ~µs. For big
enumerations (`∀ m : Fin (2^18)`) the levers are different from the kernel
case: (a) never touch `Finset`/`Fintype` in the per-item body —
`Finset.univ.filter …|>.card` rebuilds the universe multiset *per item*
(~2 ms); restate counts as `Nat` popcounts and prove
`card_support_eq_natWt`-style bridges once (`Z3Z6/MaskDefs.lean`); (b)
tabulate everything the body reads as *numeric literals* certified by one
`native_decide`/`decide` (`bndRowsLit_correct`) — a computed `def` can be
re-evaluated per reference; (c) derive the human-readable statement from the
mask-form sweep through the bridges, keeping the public theorem byte-identical
(`Z3Z6/Sweep*.lean`, ~59 min → ~7 min CPU each). `decide +kernel` is NOT an
upgrade at this scale: per-item kernel reduction through `List` folds costs
about the same and the 2^18-deep `decidableBallLT` recursion risks the C
stack. Floor: ~100+ interpreted applies per item is the practical minimum for
proof-carrying structures.

## Mechanical fixes for common gotchas

These are quick-lookup items for failures that have a definite fix once
recognized.

### `if c then 1 else 0` residual goal closer

When `simp` leaves a goal of the form `if c then 1 else 0 = …`, the
common closer is:

```lean
split_ifs <;> simp_all (config := {decide := true}) <;>
  first | rfl | exact absurd rfl ‹_›
```

### `Finset.card` of `{a, b, c, d}` with all-pairwise-distinct hypotheses

```lean
simp_all +decide [Finset.filter_eq', Finset.filter_or,
  Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton]
```

As of mathlib v4.30 `simp_all` picks up the `Ne` hypotheses (in both
directions) from context automatically. The older guidance to pass
`h₁, h₂.symm, …` explicitly is stale and now triggers
`linter.unusedSimpArgs`.

### `simp_all` with bidirectional hypotheses can erase what you need

If a hypothesis is a `↔` like `hfilt_eq : P ↔ Q`, `simp_all` may rewrite
`Q` back to `P` in a subgoal you wanted to keep simplified. Workaround:
`clear hfilt_eq` (or rename to a one-shot `have`) before `simp_all`.

### Ambiguous overloaded name (`_root_` qualification)

E.g. `mul_assoc` is ambiguous between `_root_.mul_assoc` and
`NQubitPauliGroupElement.mul_assoc` when `open NQubitPauliGroupElement`
is in scope. Qualify with `_root_.` (or the specific namespace). Trigger:
`open NQubitPauliGroupElement` near the top of a `Codes/*.lean` file
shadows several mathlib names. Same applies to `one_mul` / `mul_one`.

### `rw [one_mul, mul_one]` fails after `Subgroup.closure_induction`

The goal is `(fun y _ => …) 1 ⋯`, unreduced. Add a `change` step to
beta-reduce first — see `Homological/LogicalCorrespondence.lean:280-282`
for the canonical pattern:

```lean
· change (1 : NQubitPauliGroupElement X.numQubits) * X.chainXOperator c =
    X.chainXOperator c * 1
  rw [one_mul, mul_one]
```

### `HMul` instance failure between two defeq Pauli types

E.g. `NQubitPauliGroupElement (numQubits L)` vs.
`NQubitPauliGroupElement (rotatedSurfaceHomologicalCode L).numQubits`:
`*` resolves by syntactic type match, not defeq through abbreviations.

Fix by typing the local lemma signature consistently with whichever form
the proof body uses more. When the proof body multiplies abstract
`vertexStabOf` / `faceStabOf` against a parameter `g`, declare `g` at
`(rotatedSurfaceHomologicalCode L).numQubits` — callers can pass
`NQubitPauliGroupElement (numQubits L)` (defeq).

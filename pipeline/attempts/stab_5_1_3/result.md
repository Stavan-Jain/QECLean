# Result: [[5,1,3]] five-qubit perfect code (Laflamme 1996)

**Status:** `pr-ready`
**Branch:** `worktree-agent-aa2f5308c26453301`
**Final file:** `QEC/Stabilizer/Codes/Small/FiveQubit_5_1_3.lean` (740 LoC)
**Sorries closed:** 23 / 23 (0 blocked)
**Build:** `lake build QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3` clean

## What was formalized

The full Knill-Laflamme-Miquel-Paz-Zurek five-qubit perfect code, the
smallest single-error-correcting stabilizer code:

- Four generators `g₁ = XZZXI, g₂ = IXZZX, g₃ = XIXZZ, g₄ = ZXIXZ`
  (cyclic shifts of `XZZXI`)
- All six pairwise commutations via the parity-of-anticommuting-positions
  criterion (§4–5)
- `−I ∉ Subgroup.closure generators` (§6, the non-CSS gap-1 helper)
- Generator independence + phase-zero, packaged as
  `StabilizerCode 5 1` with the trimmed generator list (§7–9, §13)
- Logical operators `X̄ = XXXXX, Z̄ = ZZZZZ`, with anticommutation and
  centralizer membership (§10–12)
- **Distance theorem `code_has_distance_three`:** distance is exactly 3
  (§14), with witness `logicalX_w3 = IYYIX` (the operator part of
  `logicalX * g₁`, with phase 2 — weight 3).

The five-qubit code is the **first non-CSS code** in the repo. Each
generator carries both `X` and `Z` factors, so several CSS shortcuts
do not apply. This surfaced three forward-investment gaps that have
now been filled at the Core level and will amortize across all future
non-CSS codes.

## Core infrastructure added (forward-investment)

### 1. `negIdentity_not_mem_of_indep_phase_zero_commute` (Gap 1)

**Where:** `QEC/Stabilizer/Framework/Symplectic/SymplecticSpan.lean`

The CSS argument `CSS.negIdentity_not_mem_closure_union` only handles
generator sets that split cleanly into commuting Z-type / X-type subsets.
The new general-form helper takes any phase-0 generator list whose
check-matrix rows are linearly independent and whose generators
pairwise commute, and shows `−I` is not in the closure.

This is what the [[5,1,3]] §6 proof now calls.

### 2. `weightTwoAt` + `no_weight_two_mem_centralizer_of_anticommute_witness` (Gap 2)

**Where:** `QEC/Stabilizer/Framework/Core/CSS/CSSDistance.lean`

The pre-existing `no_weight_one_*` helper handles d = 2 (e.g.
[[4,2,2]]). For d = 3 we additionally rule out weight-2 centralizer
elements. The weight-2 analog mirrors the weight-1 proof exactly:
`weight g = 2` extracts a two-element support; the anticomm-witness
hypothesis at those two qubits provides a generator whose anticommute
with `g` contradicts `g ∈ centralizer`.

### 3. Computable `DecidableEq` + `Decidable Anticommute` (Stage-4 follow-up)

**Where:**
- `QEC/Stabilizer/Foundations/PauliGroup/Representation.lean` — the *operator-level*
  `DecidableEq (NQubitPauliOperator n)`, **global** instance (clean
  computable replacement of the previous `Classical.decEq`).
- `QEC/Stabilizer/Codes/Small/FiveQubit_5_1_3.lean` — the *group-element-level*
  `DecidableEq (NQubitPauliGroupElement n)` and `Decidable (Anticommute p q)`,
  **`local instance`** declarations scoped to this file only.

The group-element instances were originally placed globally in
`PauliGroup/Commutation.lean`, but that **broke** the `native_decide`
synthesis in `RotatedSurfaceCode3.lean`'s `weight_2_pairs_span_coeffs`
proof — adding a global `DecidableEq (NQubitPauliGroupElement n)`
disrupted the standard Pi-decidability chain that RSC3's synthesis was
silently relying on. They were moved to `local instance` in the
follow-up fix commit `df35c94`. See the "Lessons learned" section
below.

The previous `noncomputable instance : DecidableEq (NQubitPauliOperator
n) := Classical.decEq _` was replaced by the natural computable
instance via the underlying function type `Fin n → PauliOperator`:

```lean
instance : DecidableEq (NQubitPauliOperator n) :=
  inferInstanceAs (DecidableEq (Fin n → PauliOperator))
```

This is downstream-compatible (the existing `if p = q then …`
trace-formula in `NQubitPauliOperator.trace_mul` still works), but now
`decide` can reduce equality of n-qubit Pauli operators in the kernel.

A field-wise `DecidableEq (NQubitPauliGroupElement n)` then derives,
and `Decidable (Anticommute p q)` follows by unfolding to the
underlying equality. The Anticommute instance is marked `noncomputable`
only because `Mul` on `NQubitPauliGroupElement` is itself noncomputable
— but the kernel still reduces `decide` through it. **`native_decide`
does not work** for the same reason, so prefer `decide`.

### Why this matters for future non-CSS codes

Before this work, the only way to prove `Anticommute p q` for two
specific Pauli group elements was to invoke
`pauli_anticomm_odd_anticommutes` and then build an explicit Finset
of the anticommuting qubit positions — about 7-10 LoC per case. For
a distance-3 code, ruling out weight-1 and weight-2 logicals needs
105 such cases, which would total ~1000 LoC of mechanical witness
plumbing.

With `decide` working on `Anticommute`, each case becomes a one-line
`by decide`. The full [[5,1,3]] weight-{1,2} witness tables fit in
~100 LoC via a `fin_cases <;> first | … | by decide` pattern. The
same pattern will close the next non-CSS code's distance proof in
roughly the same LoC budget.

## Tactic patterns worth promoting to `CLAUDE.md`

(See the new entries proposed in the followup commit on `CLAUDE.md`.)

### Decidable Anticommute via field-wise equality

`Anticommute p q` is definitionally `p * q = minusOne n * (q * p)`, an
equality between two `NQubitPauliGroupElement n` values. With

- a computable `DecidableEq (NQubitPauliOperator n)` (via the underlying
  `Fin n → PauliOperator` function type), and
- a field-wise `DecidableEq (NQubitPauliGroupElement n)`,

the goal `Anticommute p q` is `decide`-able in the kernel, even though
the `Mul` instance is noncomputable. The `Decidable Anticommute`
instance itself must be marked `noncomputable`, but kernel reduction
sees through that. `native_decide` does **not** work — prefer `decide`.

### Backtracking generator search via `first | by decide | …`

For an anti-witness table like

```lean
∀ i : Fin n, ∀ P : PauliOperator, P ≠ .I →
  ∃ g ∈ generators, Anticommute (weightOneAt i P) g
```

the standard pattern is

```lean
fin_cases i <;>
  (match P, hP with
   | .X, _ => first
     | exact ⟨g₁, by simp [generators], by decide⟩
     | exact ⟨g₂, by simp [generators], by decide⟩
     | …
   | .Y, _ => …
   | .Z, _ => …
   | .I, hP => exact (hP rfl).elim)
```

`first` backtracks across generators by `decide` — wrong choices fail
cleanly thanks to the kernel-reducible `Decidable Anticommute`. Trim
unused generator branches (those `linter.unusedTactic` flags) to keep
the file lint-clean.

The weight-2 analog wraps `fin_cases i <;> fin_cases j` inside each
non-identity `(P, Q)` match arm, with the diagonal `i = j` cases
discharged by `exact absurd rfl hij`.

## Files changed (compact summary)

| File | Change | LoC delta |
|------|--------|-----------|
| `QEC/Stabilizer/Foundations/PauliGroup/Representation.lean` | computable `DecidableEq` on `NQubitPauliOperator` (global) | +3 / -2 |
| `QEC/Stabilizer/Foundations/PauliGroup/Commutation.lean` | net no-op after locality fix; carries a comment explaining why | +6 / 0 |
| `QEC/Stabilizer/Framework/Symplectic/SymplecticSpan.lean` | Gap 1 (non-CSS −I lemma) | (in previous Stage-4 session) |
| `QEC/Stabilizer/Framework/Core/CSS/CSSDistance.lean` | Gap 2 (weight-2 witness helper) | (in previous Stage-4 session) |
| `QEC/Stabilizer/Codes/Small/FiveQubit_5_1_3.lean` | full Stage-4 closure (T2, T9) + local `DecidableEq`/`Anticommute` instances | +179 |

## Commits on branch

```
df35c94 fix(stab_5_1_3): scope Decidable instances locally to unblock RSC3 build
69f8ea3 fix(RotatedSurfaceCode3): split XGenerators_are_XType simp call
33dd7be feat(stab_5_1_3): close T9 — five-qubit perfect code has distance 3
d822ac5 feat(stab_5_1_3): weight-2 anticomm witness (90 cases)
46ee4a3 feat(stab_5_1_3): computable DecidableEq + weight-1 anticomm witness
8c1a843 feat(commutation): computable DecidableEq + Decidable Anticommute
12259b0 feat(stab_5_1_3): weight-3 witness + Gap 2 Core helper; T9 close-but-blocked
7cfc2a8 feat(stab_5_1_3): close T2 negIdentity_not_mem via new SymplecticSpan helper
2c370a7 wip(stab_5_1_3): close 21/23 sorries (warm-ups + commutations + centralizer)
eb8ea80 skeleton(stab_5_1_3): Stage-2 baseline (23 sorries, 394 LoC, first non-CSS code)
```

## Lessons learned

### Global vs. local typeclass instances — when to scope `local`

The most consequential lesson of this pilot. The Stage-4 agent added
`instDecidableEqNQubitPauliGroupElement` and `decidableAnticommute` as
**global** instances in `PauliGroup/Commutation.lean`, intending them to
service any future non-CSS code's distance proof. Both instances are
well-typed and themselves computable (for `DecidableEq`) or noncomputable
(for `Anticommute`, by design).

What went wrong: the addition of a global `DecidableEq
(NQubitPauliGroupElement n)` perturbed Lean's typeclass synthesis for a
seemingly unrelated proposition in `RotatedSurfaceCode3.lean`. The
`weight_2_pairs_span_coeffs` proof there uses `native_decide` on a
`∀-∃` proposition whose body involves only `Fin n → ZMod 2` equality
— no `NQubitPauliGroupElement` equality whatsoever. Yet the new
instance, by entering the global pool, disrupted the synthesis path
that RSC3's `native_decide` was silently relying on, causing it to fail
to synthesise a `Decidable` instance at all.

The signature of the failure was distinctive: not "instance is
noncomputable", not "`Classical.choice` stuck during reduction", but
"failed to synthesize Decidable" — the synthesizer couldn't even start.
Running `classical decide` revealed that with `Classical.propDecidable`
in scope a `Decidable` was found, but reduction hit `Classical.choice`.

**Rule of thumb:** if an instance services exactly one concrete code
file's proof, declare it `local instance` inside that file. Reserve
global instances in `PauliGroup/`, `Core/`, `BinarySymplectic/` for
genuinely reusable typeclass content. **Always run a whole-repo
`lake build` after adding a global instance**, not just the affected
file's build — global instance changes have non-local effects on
typeclass synthesis.

The locality fix is in commit `df35c94`. See also the new entry
in `CLAUDE.md` under "Things that broke recently in v4.30".

### Decidable Anticommute requires a careful balance

The Stage-4 [[5,1,3]] proof uses `by decide` on `Anticommute p q` for
concrete Pauli group elements. This requires a `Decidable Anticommute`
instance backed by a *computable* `DecidableEq (NQubitPauliGroupElement n)`,
which in turn requires a computable `DecidableEq (NQubitPauliOperator n)`.

The chain works, but only when:
1. `DecidableEq (NQubitPauliOperator n)` is computable (it now is, in
   `Representation.lean`, globally — this is safe);
2. `DecidableEq (NQubitPauliGroupElement n)` is computable AND in scope
   (now `local` in `FiveQubit_5_1_3.lean`);
3. `Decidable (Anticommute p q)` is in scope (now `local` in the same
   file).

For future non-CSS codes that want the same shortcut, copy the two
`local instance` blocks from `FiveQubit_5_1_3.lean`'s preamble.
Eventually a cleaner abstraction is worth designing (e.g., a `local`
opener pattern via `open scoped`), but for now the literal copy is the
right call.

## Next steps

- Open PR against `main` once the rest of the worktree is verified.
- Update `pipeline/queue.md` to reflect [[5,1,3]] as done; refresh
  scoring on the next dependent codes (the EC Zoo `stab_*_1_3` family
  becomes much cheaper now that the non-CSS infrastructure exists).
- Consider promoting the **Decidable Anticommute** and **`fin_cases <;>
  first` witness pattern** notes to `CLAUDE.md` so future non-CSS
  Stage-4 sessions discover them up front.

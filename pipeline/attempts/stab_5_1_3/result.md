# Result: [[5,1,3]] five-qubit perfect code (Laflamme 1996)

**Status:** `pr-ready`
**Branch:** `worktree-agent-aa2f5308c26453301`
**Final file:** `QEC/Stabilizer/Codes/FiveQubit_5_1_3.lean` (740 LoC)
**Sorries closed:** 23 / 23 (0 blocked)
**Build:** `lake build QEC.Stabilizer.Codes.FiveQubit_5_1_3` clean

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

**Where:** `QEC/Stabilizer/BinarySymplectic/SymplecticSpan.lean`

The CSS argument `CSS.negIdentity_not_mem_closure_union` only handles
generator sets that split cleanly into commuting Z-type / X-type subsets.
The new general-form helper takes any phase-0 generator list whose
check-matrix rows are linearly independent and whose generators
pairwise commute, and shows `−I` is not in the closure.

This is what the [[5,1,3]] §6 proof now calls.

### 2. `weightTwoAt` + `no_weight_two_mem_centralizer_of_anticommute_witness` (Gap 2)

**Where:** `QEC/Stabilizer/Core/CSSDistance.lean`

The pre-existing `no_weight_one_*` helper handles d = 2 (e.g.
[[4,2,2]]). For d = 3 we additionally rule out weight-2 centralizer
elements. The weight-2 analog mirrors the weight-1 proof exactly:
`weight g = 2` extracts a two-element support; the anticomm-witness
hypothesis at those two qubits provides a generator whose anticommute
with `g` contradicts `g ∈ centralizer`.

### 3. Computable `DecidableEq` + `Decidable Anticommute` (Stage-4 follow-up)

**Where:** `QEC/Stabilizer/PauliGroup/Representation.lean` (the operator
DecidableEq) and `QEC/Stabilizer/PauliGroup/Commutation.lean` (the
Pauli group element DecidableEq + Anticommute Decidable).

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
| `QEC/Stabilizer/PauliGroup/Representation.lean` | computable `DecidableEq` on `NQubitPauliOperator` | +3 / -2 |
| `QEC/Stabilizer/PauliGroup/Commutation.lean` | `DecidableEq` on `NQubitPauliGroupElement` + `Decidable Anticommute` | +20 / 0 |
| `QEC/Stabilizer/BinarySymplectic/SymplecticSpan.lean` | Gap 1 (non-CSS −I lemma) | (in previous Stage-4 session) |
| `QEC/Stabilizer/Core/CSSDistance.lean` | Gap 2 (weight-2 witness helper) | (in previous Stage-4 session) |
| `QEC/Stabilizer/Codes/FiveQubit_5_1_3.lean` | full Stage-4 closure (T2, T9 specifically) | +145 |

## Commits on branch

```
33dd7be feat(stab_5_1_3): close T9 — five-qubit perfect code has distance 3
d822ac5 feat(stab_5_1_3): weight-2 anticomm witness (90 cases)
46ee4a3 feat(stab_5_1_3): computable DecidableEq + weight-1 anticomm witness
8c1a843 feat(commutation): computable DecidableEq + Decidable Anticommute
12259b0 feat(stab_5_1_3): weight-3 witness + Gap 2 Core helper; T9 close-but-blocked
7cfc2a8 feat(stab_5_1_3): close T2 negIdentity_not_mem via new SymplecticSpan helper
2c370a7 wip(stab_5_1_3): close 21/23 sorries (warm-ups + commutations + centralizer)
eb8ea80 skeleton(stab_5_1_3): Stage-2 baseline (23 sorries, 394 LoC, first non-CSS code)
```

## Next steps

- Open PR against `main` once the rest of the worktree is verified.
- Update `pipeline/queue.md` to reflect [[5,1,3]] as done; refresh
  scoring on the next dependent codes (the EC Zoo `stab_*_1_3` family
  becomes much cheaper now that the non-CSS infrastructure exists).
- Consider promoting the **Decidable Anticommute** and **`fin_cases <;>
  first` witness pattern** notes to `CLAUDE.md` so future non-CSS
  Stage-4 sessions discover them up front.

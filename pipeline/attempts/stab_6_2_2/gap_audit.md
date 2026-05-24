# Gap audit: [[6,2,2]] C_6 code

This file identifies the anticipated trouble spots in the C_6
formalization. Most are minor mechanical concerns; none are blocking.

## Repo gaps (this code surfaces / requires new abstractions)

### Nothing genuinely new

C_6 is the *fourth* user of `hasCodeDistance_two_of_anticommute_witness`,
the *second* k = 2 CSS code, and the *second* multi-Z-stabilizer CSS
code. Every primitive and pattern it needs already exists.

### Minor: 3-way partition pattern in `weight_one_anticomm_witness`

`CSS_4_1_2.lean` introduced the `hi_dichotomy` (2-way partition for
qubits covered by `S_Z1` vs `S_Z2`). C_6 needs a **3-way** partition:
```
hi_trichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5)
```

This is not a *gap* per se — it's a direct extension of `hi_dichotomy`
to one more case. But if the pattern recurs (e.g. for larger Knill codes
or GOY r ≥ 2), it may be worth documenting in `docs/lean-patterns.md` as
a generalization of the 2-way pattern.

**Recommended action**: leave the trichotomy inline in `SixQubit_6_2_2.lean`
for now; promote to a doc patterns entry when a 4-way / parametric
version arrives.

### Minor: `logical_commute_cross` 4-case `fin_cases` dispatch

The 4-case dispatch in the `logical_commute_cross` field of
`StabilizerCode 6 2` is identical in shape to
`FourQubit_4_2_2.stabilizerCode` (lines 457-467). If a third k = 2 CSS
code arrives, a `LogicalQubitOps.cross_commute_pair` smart constructor
could collapse the four `refine ⟨..., ..., ..., ...⟩` cases into one
named lemma per pair `(ℓ, ℓ') ∈ Fin 2 × Fin 2`. **Not blocking**;
leave for a future refactor when k ≥ 3 makes the boilerplate
intolerable.

## Mathlib gaps (lemmas not in mathlib v4.30)

**None identified.** All required mathlib lemmas (`Subgroup.closure`,
`Subgroup.forall_comm_closure_iff`, `Subgroup.mem_centralizer_iff`,
`Finset.mem_filter`, `Finset.card_*`, `Fin.cases`, `mul_assoc`,
`one_mul`, `mul_one`, `mul_inv_cancel`) are in v4.30.

## Likely "BLOCKED(<reason>)" sorries

**None anticipated.** Every theorem in the skeleton has a clear,
existing-template-based closing strategy.

## Mechanical risks (Stage-4 specific)

### 1. Stabilizer support structure for T31 dispatch

**Risk.** `S_Z1` and `S_Z2` **overlap** at qubits {0,1}, **disagree** at
{2,3} (only S_Z1) and {4,5} (only S_Z2). This is NOT a clean disjoint
partition — qubits {0,1} are ambiguous for the weight-1 witness
function.

**Mitigation**: in T31, dispatch on a 3-way trichotomy and assign:
- `i ∈ {0,1}` → pick `S_Z1` (arbitrary choice; could equally pick
  `S_Z2`).
- `i ∈ {2,3}` → pick `S_Z1`.
- `i ∈ {4,5}` → pick `S_Z2`.

The helper lemma `weightOneAt_anticomm_S_Z1` accepts the 4-disjunction
hypothesis `i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3` (the support of `S_Z1`), and
the witness function dispatches the canonical choice.

**Equivalent alternative (slightly cleaner)**: pick `S_Z2` for `i ∈ {0,1}`
instead. Either way, document the canonical choice in the witness
function's docstring.

### 2. `pauli_comm_even_anticommutes` filter Finset sizes

For the cross-commutation theorems T3-T6, the filter Finsets are:
- T3: `{0, 1, 2, 3}` (size 4)
- T4: `{0, 1}` (size 2)
- T5: `{0, 1}` (size 2)
- T6: `{0, 1, 4, 5}` (size 4)

All sizes even ⇒ commute, which is the expected CSS structural fact.

**Risk**: the `ext i; fin_cases i <;> simp [...]` proof step in each
filter-equality lemma now runs `fin_cases i` over `Fin 6` (6 cases)
instead of `Fin 4` (4 cases). `simp [Finset.mem_filter, ...]` should
still close each case in milliseconds.

**Mitigation**: if `simp` is slow on the 6-case branch, fall back to
`omega` or explicit `decide` after the `simp`-induced normalization.
No real risk; the [[5,1,3]] proof in `FiveQubit_5_1_3.lean` does
similar combinatorics for n = 5.

### 3. Logical-operator weight irregularity

Unlike `FourQubit_4_2_2.lean`'s clean weight-2 logicals
(`IXIX, IIXX, IIZZ, IZIZ` — all weight 2), C_6's logicals from Knill 2004
have mixed weights: `X_L=IIXXII` (weight 2), `Z_L=ZIIZZI` (weight 3),
`X_S=IXIXXI` (weight 3), `Z_S=IIIIZZ` (weight 2).

**Risk**: the `pauli_comm_componentwise` tactic (used for both-X-type
and both-Z-type commutations) may be slower or fail on weight-3
operators if the underlying decision procedure has quadratic blowup.

**Mitigation**: if `pauli_comm_componentwise` fails, fall back to
`pauli_comm_even_anticommutes` + explicit Finset (which always works,
just more verbose). The repo's existing usage of
`pauli_comm_componentwise [logicalX_1, X1]` etc. covers up to weight-4
operators on `Fin 4`, so weight-3 on `Fin 6` should be fine.

### 4. Even-count weight-2 filter shapes for cross-logical commutation

T19 (`X_S = IXIXXI` vs `Z_L = ZIIZZI`) has anticommute filter `{3, 4}`
(size 2). Q3 has X·Z, Q4 has X·Z, both anticommute pairwise; counts to 2
(even) ⇒ commute. T18 (`X_L` vs `Z_S`) has empty filter (size 0, even ⇒
commute). The other two (T17, T20) are both X-type or both Z-type so use
componentwise.

**Risk**: writing the explicit Finset `{3, 4}` in Lean requires
unambiguous Fin 6 literals. Use `({3, 4} : Finset (Fin 6))` with
type annotation if needed.

**Mitigation**: copy the explicit-type annotation pattern from
`CSS_4_1_2.S_Z1_comm_S_X1` (line 145: `({0, 1} : Finset (Fin 4))`),
just changing the `Fin 4` to `Fin 6`.

### 5. `decide` on `rowsLinearIndependent` for n = 6, 4 rows

The check-matrix for C_6 is 4×12 over GF(2). `decide` should close
this in well under a second (CSS_4_1_2's 3×8 matrix closes nearly
instantly). **No risk.**

### 6. Picking `logicalX_1 = IIXXII` (weight 2) as the witness for `code_has_distance_two`

The distance proof needs ONE witness `g` with `IsNontrivialLogicalOperator
g stabilizerCode.toStabilizerGroup` AND `weight g = 2`. Both `logicalX_1`
(weight 2) and `logicalZ_2` (weight 2) qualify. Pick `logicalX_1` for
canonical alignment with `CSS_4_1_2.code_has_distance_two`'s use of
`logicalX`.

The `by decide` weight check at the end of the witness construction
needs `weight (logicalX_1 : NQubitPauliGroupElement 6) = 2`, where
`logicalX_1.operators = ((identity 6).set 2 X).set 3 X`. The `weight`
function counts non-I entries; for 6 qubits with two X-positions, the
count is 2. **No risk** — `decide` reduces this immediately.

### 7. `linter.unusedSimpArgs` from `NQubitPauliOperator.identity`

Per `docs/lean-patterns.md` § "`NQubitPauliOperator.identity` in simp
sets":
- Drop `identity` from simp set when the generator's `.set` chain
  fully covers `Fin n`.
- Keep `identity` for partial-coverage generators.

For C_6 with n = 6:
- `S_Z1 = ZZZZ II`: covers qubits {0,1,2,3}, leaves {4,5} → fall through
  to `identity`. **Keep `identity` in simp.**
- `S_Z2 = ZZ II ZZ`: covers {0,1,4,5}, leaves {2,3} → **keep `identity`**.
- `S_X1 = XXXX II`: covers {0,1,2,3}, leaves {4,5} → **keep `identity`**.
- `S_X2 = XX II XX`: covers {0,1,4,5}, leaves {2,3} → **keep `identity`**.

All 4 generators of C_6 are partial-support, so we keep
`NQubitPauliOperator.identity` in **every** generator-type-check
simp invocation (unlike `[[4,2,2]]`'s `ZZZZ`/`XXXX`, which fully cover
`Fin 4` and drop `identity`).

### 8. `pauli_comm_componentwise` lemma signature

The tactic takes a list of generator names:
`pauli_comm_componentwise [logicalX_1, logicalX_2]`. For T17 (X_L vs
X_S) and T20 (Z_L vs Z_S), this is the right path. For T18 (X_L vs Z_S
with disjoint supports), we could use the same tactic — both factors
commute at every qubit (one is I, the other can be anything, or both
are the same Pauli at qubits 0,1). Should work.

**Risk**: if `pauli_comm_componentwise` doesn't handle mixed
X-then-Z-then-I patterns well, fall back to `pauli_comm_even_anticommutes`
with an empty Finset.

### 9. Build-time `decide` on the full skeleton (no proof yet)

The skeleton ends every theorem in `sorry`. `lake build` of the new
module should produce only "declaration uses sorry" warnings — no
errors. **Confirm at end of Stage 2** (see success criteria).

## Summary

C_6 surfaces **no genuine gaps** in the repo or in mathlib. The
mechanical risks above are all standard for any small CSS code and
already have documented mitigations in `CLAUDE.md`,
`docs/lean-patterns.md`, and the existing `FourQubit_4_2_2.lean` /
`CSS_4_1_2.lean` templates. Stage 4 should close all 33 sorries in
~3 hours of attentive work.

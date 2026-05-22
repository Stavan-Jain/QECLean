# Gap audit: [[4,2,2]] Four-qubit code

## Repo gaps (this code surfaces / requires new abstractions)

- **k ≥ 2 ergonomics on `logical_commute_cross`.** The structure field
  `StabilizerCode.logical_commute_cross` has the shape
  ```lean
  ∀ ℓ ℓ', ℓ ≠ ℓ' →
    (xx-eq ∧ xz-eq ∧ zx-eq ∧ zz-eq)
  ```
  which is the only field in `StabilizerCode` that genuinely needs `k ≥ 2`.
  The Steane7 and Shor9 packagings discharge it with
  `fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim`. For [[4,2,2]] we need to
  actually case-split on `(ℓ, ℓ')`. This will be slightly awkward because the
  hypothesis is a single ∧-of-4-eqs. Suggested helper (out of scope for
  Stage 2): a smart constructor `LogicalQubitOps.cross_commute_pair` that takes
  the four equations as separate arguments and builds the bundled conjunction.
  Not a blocker — just makes Stage 4's packaging proof cleaner.
- **Small-distance d = 2 enumeration utility.** There is no existing helper
  for "every weight-1 Pauli anticommutes with at least one of the given
  stabilizers". Could be a one-shot in this file, or a reusable lemma
  ```lean
  theorem distance_two_from_full_X_full_Z (g : NQubitPauliGroupElement n) ...
  ```
  if more future codes need it. Defer to Stage 4 to decide based on actual
  proof cost.
- **`HasCodeDistance.detects_errors` / `corrects_errors` translations.** The
  EC Zoo protection statement is "detects single-qubit errors" and "fails to
  correct because ⌊(d−1)/2⌋ = 0". The repo defines `HasCodeDistance` (this is
  fine for Stage 2) but does **not** package the
  "detects t errors iff t < d" theorem at the centralizer-error level.
  Stage 4 could add a small lemma `detects_errors_of_distance` if there is
  appetite; it's a 2-3 line theorem from `HasCodeDistance.min_weight` +
  `IsNontrivialLogicalOperator` plus the standard "syndrome
  distinguishability" framing. **Not required** for the Stage 2 outputs to
  parse.

## Mathlib gaps (lemmas not in mathlib v4.30)

- **None encountered.** The proof obligations all reduce to
  `Subgroup.closure_induction`, `Finset` case-bashing, and `decide`/`native_decide`
  on small Fin 4 problems, all of which mathlib already provides cleanly.
  Mathlib's `Subgroup.IndependentGenerators`, abelian closure, and the
  Submodule-span / `Finset.card` lemmas used elsewhere in the repo all apply
  unchanged.

## Likely "BLOCKED(<reason>)" sorries

**None expected.** Every theorem in the skeleton has a documented and
mechanical-feeling proof strategy (case-bash + `decide`/`native_decide` for the
small cases, established Steane7-style pattern for the structural parts).
The hardest theorem T13 (distance) decomposes into a 12-case enumeration
that should be trivially `decide`-able.

If a sorry does end up `BLOCKED`, the two most likely candidates are:

1. **T13 distance** if `native_decide` is too slow on `HasCodeDistance` and
   the manual enumeration runs into `IsNontrivialLogicalOperator` defeq
   issues (operator-part vs full element). Workaround: invoke
   `anticommutes_imp_not_isPauliLogicalOperator` per weight-1 Pauli
   explicitly, then close with `decide` per case (12 sub-cases). This is the
   `RepetitionCode3.Z_on_qubit2_operators_ne_of_mem` style of proof.

2. **T12 packaging `logical_commute_cross`** if the Fin 2 case-split on the
   ∧-of-4-eqs cannot be discharged cleanly. Workaround: spell out the four
   directed equations as separate lemmas and combine via `And.intro` chains;
   the indexed `match` over `ℓ`, `ℓ'` is just bookkeeping.

Neither is a true "BLOCKED" — both have clear fallback strategies.

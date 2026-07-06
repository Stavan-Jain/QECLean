# Gap audit: CSS code concatenation

> What this attempt requires that the repo does not yet provide, plus the
> soundness fixes the adversarial critics (distance-soundness,
> constructor/phase-soundness) imposed on the design. Each fix is tagged with
> the risk-register ID from `plan.md`.

## Repo gaps (new abstractions this attempt must introduce)

### Gap 1: operator embedding / reindexing across qubit counts (M1) — NEW
**Status: entirely missing.** `NQubitPauliOperator n := Fin n → PauliOperator`
has `get`/`set`/`pointwiseImage`, but nothing embeds a `Fin n₁` operator into a
block of `Fin (n₁·n₂)`, tensors two Paulis, or relabels via an index map. The
toric `rowMajor_injective` and `edgeToQubitIdx` are lattice-specific.

**Resolution:** author `qIdx`/`blockOf`/`posOf`/`embedBlockOp`/`embedBlock` plus
the weight/support/commutation lemmas (M1). Fiddly but bounded; the only real
friction is phase tracking — resolved by the zero-phase convention (see R2).

### Gap 2: inner-centralizer classification `centralizer_classify_of_k1` (M4) — NEW, the long pole
**Status: missing.** No `centralizer = ⟨stabilizer, X̄, Z̄⟩` theorem exists. The
distance lower bound genuinely requires it (the weak "logical-or-stabilizer
dichotomy" is **insufficient** — see R1). HasCodeDistance alone (min weight of a
nontrivial logical) does not give the per-block decomposition.

**Resolution:** **buildable on the existing symplectic span bridge**, not from
scratch. `SymplecticSpan.lean` already provides `mem_closure_implies_symp_in_span`,
`exists_mem_closure_of_symp_in_span`, `not_mem_subgroup_of_symp_not_in_span`.
M4 assembles them with `SymplecticOrthogonal` into the dim-2 (k=1) classification.
**Schedule M4 in parallel with M2/M3; spike the n=7 Steane case first** to
validate the dimension-2 claim before the parametric proof.

### Gap 3: block-restriction + induced-outer correspondence (M5) — NEW
**Status: missing**, concatenation-specific. `restrictBlock`, `inducedOuter`,
and the proof that the induced operator is a *nontrivial* outer logical. Mirror
the toric correspondence-file convention.

### Gap 4: the `concatenate` constructor and `concat_hasCodeDistance` (M3, M6) — NEW
**Status: missing.** `StabilizerCode` has no product/concatenation constructor.

## Mathlib gaps
**None expected.** The new work uses `Finset.filter`/`card`, `Fin`-arithmetic +
`omega`, `Nat.mul_pos`, parity (`Even`/`Odd`), and `Subgroup.closure_induction`
— all standard. The hard content is repo-local, not mathlib-local.

## Adversarial-critic soundness fixes (folded into the plan)

These changed the *design*, not just the schedule. Each was a real defect in
the initial tier designs caught before any Lean was written.

### Fix R2 (BLOCKING) — unify the phase convention to zero-phase
The initial Tier-0 design carried a group-level `embedBlock_mul` whose truth
depends on an unstated phase convention. **Resolution:** `embedBlock`/`promoteE`
are `ofOperator (…)` (phase 0 definitionally, `NQubitElement.lean:110`). The
group-level multiplicativity lemma is **deleted** and restated as the
operator-level, phase-free `mulOp_embedBlockOp_operators`. Commutation goes
through the parity lemmas only — never a homomorphism route (also kills R8).

### Fix R3 (BLOCKING) — promote over typed sublists, never the raw list
`promoteSingle` has a `Y ↦ I` branch that is lossy/unsound if fed an arbitrary
operator. **Resolution:** route promotion through `outerZ ++ outerX` (CSS-typed),
carried back to `Cout.generatorsList` by an `outer_split` permutation. Then
`promoteSingle_noY_of_isXType/isZType` prove the Y-branch unreachable. Same for
the inner logical reps: their CSS-typing and phase-0-ness are **explicit
`ConcatCSSData` hypotheses** (`innerLogX_isX`, `innerLogX_phaseZero`, …),
discharged per-instance (trivial for Steane/Shor).

### Fix R4 (SERIOUS) — restrictions can be Y-class; do not CSS-type them
`restrictBlock b L` can carry the `X̄₁Z̄₁` (Y) class on a block. **Resolution:**
every "this operator shares a stabilizer's operator-part ⇒ it *is* that
stabilizer" step uses the phase/Y-agnostic `mul_inv_operators_identity_of_eq_operators`
(`NQubitElement.lean:292`) + `commutes_of_operators_identity` (`Commutation.lean:402`),
**not** any CSS-only `z_mul_x`-style lemma.

### Fix R6 (SERIOUS) — verify the parity lemma in isolation first
The "promoted generators commute on the nose" claim rests entirely on
`promote_anticommute_filter_card_parity`. **Resolution:** build and verify it
standalone before any of the commutation cases. The odd-parity atom is
`(Cin.logicalOps 0).anticommute` via `anticommutes_iff_odd_anticommutes`
(phase-blind, airtight).

### Fix R5 (SERIOUS) — independence has a pre-built primary route + a fallback
The promoted/inner separation `symp(X̄₁) ∉ span(inner rows)` was flagged as
net-new. **Resolution:** it is `not_mem_subgroup_of_symp_not_in_span`
(`SymplecticSpan.lean:111`), which exists. Fallback if the parametric assembly
overruns: accept `rowsLinearIndependent_concat` as a `ConcatCSSData` field,
discharged per-instance (`native_decide` at n=49 via `rowsLinearIndependent_iff_forall`).

## Likely "BLOCKED(<reason>)" sorries (anticipated)
- **M4 `centralizer_classify_of_k1`** is the highest-uncertainty item. If the
  parametric dim-2 symplectic assembly proves harder than ~350 LOC, the
  fallback is to ship M1–M3 (the constructor, which needs only commutation +
  independence — both provable *without* M4) and leave M4–M6 as a follow-on.
  M5/M6 must **not** be attempted before M4 closes — they are unsound otherwise.

## Architectural / future-cleanup notes
1. **Embedding primitives live in `Framework/Concatenation/`, not `Codes/Concat/`**
   — they have no Codes dependency (layering). Only constructor/restriction/
   distance/instance live under `Codes/Concat/`.
2. **M4 is reusable framework content.** `centralizer_classify_of_k1` is useful
   well beyond concatenation (any k=1 code's logical/centralizer reasoning).
   Place it in `Framework/Symplectic/CentralizerStructure.lean` and run a
   whole-repo `lake build` (global-content discipline).
3. **k₁ ≥ 2 and non-CSS** are deliberate non-goals; revisit only after the CSS
   k₁=1 path lands. Non-CSS would need the `Y ↦ Ȳ₁ = iX̄₁Z̄₁` promotion branch
   and its phase bookkeeping.
4. **A general `weight_ge_of_blocks_ge` / block-superadditivity** lemma (M1) may
   be promotable to `Foundations` if a second block-structured code appears.

# Reuse audit: CSS code concatenation

> Line numbers spot-checked against the repo on **2026-06-15** (the
> load-bearing entries below were each confirmed present at the cited line via
> `grep`). Re-verify at Stage 2/4 — they drift. The durable reference is the
> **name**, not the line.

## Directly applicable (use as-is)

### Pauli-group foundations
- `NQubitPauliOperator n := Fin n → PauliOperator`, `.identity`, `.get`, `.set`,
  `.support`, `.weight` — `Foundations/PauliGroup/NQubitOperator.lean`.
- `NQubitPauliGroupElement n` (`phasePower : Fin 4`, `operators`), `.mulOp`,
  `.weight` — `Foundations/PauliGroup/NQubitElement.lean`.
- **`ofOperator (op) : NQubitPauliGroupElement n`** with `phasePower = 0`
  — `NQubitElement.lean:110`. **Anchors the zero-phase convention (R2).**
  `embedBlock`/`promoteE` are both `ofOperator (…)`.
- **`mul_inv_operators_identity_of_eq_operators`** — `NQubitElement.lean:292`.
  Phase/Y-agnostic; backbone of M4's `mem_stabilizer_of_operators_eq` (fixes R4).

### Commutation / parity infrastructure
- **`commutes_iff_even_anticommutes`** — `Foundations/PauliGroup/Commutation.lean:142`.
  "Two Paulis commute iff the count of anticommuting qubit positions is even."
  **The core tool** for the on-the-nose commutation parity argument (M1, M3, R6).
- **`anticommutes_iff_odd_anticommutes`** — `Commutation.lean:285`. Dual; used
  for `embedBlock_anticommute_iff` and the logical anticommutation (M1, M3).
- **`commutes_of_operators_identity`** — `Commutation.lean:402`. Phase/Y-agnostic;
  pairs with `mul_inv_operators_identity_of_eq_operators` in M4 (fixes R4).
- `NQubitPauliGroupElement.Anticommute`, `.anticommutesAt`, and the
  `Decidable (Anticommute p q)` instance — `Commutation.lean` (use `decide`,
  not `native_decide`, on `Anticommute` goals).

### Symplectic span ↔ subgroup bridge (makes M4 *reuse*, not author)
All in `Framework/Symplectic/SymplecticSpan.lean`:
- **`mem_closure_implies_symp_in_span`** — line 70. Closure element ⇒ its
  symplectic vector is in the row span.
- **`not_mem_subgroup_of_symp_not_in_span`** — line 111. The independence
  separation for `generators_independent` (R5).
- **`exists_mem_closure_of_symp_in_span`** — line 120. In-span symplectic vector
  ⇒ realized by a closure element. Backbone of the M4 classification.
- **`negIdentity_not_mem_of_indep_phase_zero_commute`** — line 388. **Non-CSS**
  no-`−I` lemma (a general-form alternative to the CSS union lemma).

These four are exactly the machinery the distance-critic flagged as "net-new"
for M4/independence — they already exist. M4 assembles them into the dim-2
centralizer classification.

### CSS predicates and no-`−I`
- **`IsZTypeElement`** (`CSSPredicates.lean:150`), **`IsXTypeElement`**
  (`CSSPredicates.lean:154`), `IsZ/XTypeElement_{one,mul,inv,of_mem_closure}`
  (lines 198–252). Used for typed promotion (M2) and CSS bookkeeping.
- **`negIdentity_not_mem_closure_union`** — **`Framework/Core/CSS/CSSCommutationLemmas.lean:34`**
  (NB: in CSSCommutationLemmas, *not* CSSNoNegI — the synthesis mis-located it).
  Closes `concat_closure_no_neg_identity` (M3) on the regrouped Z∪X generator set.

### Stabilizer-code structure
- `StabilizerCode n k` (9 fields incl. `logicalOps`, `logical_commute_cross`),
  `mkStabilizerFromGenerators`, `toStabilizerGroup`
  — `Framework/Core/Stabilizer/StabilizerCode.lean` / `StabilizerGroup.lean`.
- **`GeneratorsIndependent_of_rowsLinearIndependent`** — `StabilizerCode.lean:48`.
  The bridge from check-matrix independence to `generators_independent` (M3).
- `centralizer`, `mem_centralizer_iff{,_closure}`,
  `Subgroup.forall_comm_closure_iff` — `Framework/Core/Stabilizer/`.

### Logical operators (phase/Y-agnostic — fixes R4, R10)
- `LogicalQubitOps n S` (5 fields: xOp, zOp, x/z_mem_centralizer, anticommute),
  `IsNontrivialLogicalOperator` + `IsNontrivialLogicalOperator_iff` (3 conditions),
  `xOp_nontrivial`, `zOp_nontrivial` — `Framework/Core/Logical/LogicalOperators.lean`.
- **`xOp_operators_ne_of_mem`** (`LogicalOperators.lean:227`),
  **`zOp_operators_ne_of_mem`** (`LogicalOperators.lean:267`). Discharge the
  third `IsNontrivialLogicalOperator` clause for the induced operator and the
  witness **without** CSS-typing them (R10).

### Distance
- **`HasCodeDistance C d`** (`CodeDistance.lean:28`) = `d ≥ 1` ∧ all nontrivial
  logicals of positive weight have weight ≥ d ∧ a weight-d witness exists.
- **`hasCodeDistance_of`** — `CodeDistance.lean:54`. The constructor M6 calls
  with (≥1, witness, min-weight). `StabilizerCodeWithDistance n k d` for packaging.
- `weight g := NQubitPauliOperator.weight g.operators` (count of non-I entries).

### Check-matrix decidability
- **`rowsLinearIndependent_iff_forall`** — `Foundations/BinarySymplectic/CheckMatrixDecidable.lean:24`,
  plus its `Decidable` instance. Powers the n=49 `native_decide` fallback for
  `rowsLinearIndependent_concat` (R5).

### Index machinery
- `Geometry/GridIndexing.lean` `rowMajor_injective` — precedent for the
  `qIdx : Fin n₂ × Fin n₁ → Fin (n₁·n₂)` block indexing (M1).
- mathlib `Fin.append`/`castAdd`/`natAdd`/`finProdFinEquiv` available; toric uses
  raw `Fin` arithmetic (`b·n₁ + i`) which M1 mirrors.

## Lightly adapted (existing pattern, new instance)
- **Parametric CSS packaging discipline** — `Codes/Iceberg/N.lean` (`Fact`-style
  constraint, `Fin k` logicals, parametric `rowsLinearIndependent`, the
  `logical_commute_cross` "no `fin_cases` on symbolic `Fin k`" structural trick).
  The concatenated code reuses this for k₂ logicals.
- **Parametric distance file-split** — `Codes/Toric/{Distance,Homology,
  LogicalCorrespondence{X,Z},ChainComplex}.lean`. Structural template for M5/M6:
  a combinatorial-correspondence file + a min-weight distance file. The
  concatenation analog is `inducedOuter` (correspondence) + `weight_ge_d1_mul_d2`.
- **Steane instance** — `Codes/Small/Steane7.lean` supplies `Cin = Cout` for M7
  with canonical phase-0 all-X / all-Z logical reps satisfying every
  `ConcatCSSData` typed/phase-0 hypothesis trivially.
- **Concatenation precedent** — `Codes/Small/Shor9.lean` is itself a
  concatenation (3-bit phase ∘ 3-bit flip); useful as a conceptual cross-check,
  though it is hand-built, not produced via `concatenate`.

## New, must be authored fresh (no repo analog)
See `gap_audit.md` for detail. Summary:
- **`embedBlock` / promotion operator calculus** (M1, M2) — no embed/tensor/
  relabel of Paulis across qubit counts exists today.
- **`centralizer_classify_of_k1`** (M4) — no `centralizer = ⟨stab, logicals⟩`
  theorem exists; the one genuine net-new framework result (but buildable on
  the existing `SymplecticSpan` bridge).
- **`restrictBlock` + `inducedOuter` correspondence** (M5) — concatenation-specific.
- **`concatenate` constructor** and **`concat_hasCodeDistance`** (M3, M6).

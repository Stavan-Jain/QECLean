# Reuse audit: [[6,2,2]] C_6 code

This file maps every needed primitive in `SixQubit_6_2_2.lean` to its
existing home in the repo, so Stage 4 can copy proof patterns rather
than reinvent them.

## Directly applicable (use as-is)

### Core stabilizer infrastructure
- `NQubitPauliGroupElement 6` — physical Pauli group on 6 qubits.
  [`QEC/Stabilizer/Foundations/PauliGroup/NQubitElement.lean`]
- `NQubitPauliOperator.identity`, `NQubitPauliOperator.set` — the
  `.identity` chain + `.set i P` for generator construction.
  [`QEC/Stabilizer/Foundations/PauliGroup/NQubitOperator.lean`]
- `PauliOperator.X, Y, Z, I, .IsZType, .IsXType, .mulOp` — single-qubit
  Pauli enum + predicates + multiplication table.
  [`QEC/Stabilizer/Foundations/PauliGroupSingle.lean`]
- `StabilizerGroup n` (structure) — the abstract stabilizer-group
  bundle. [`QEC/Stabilizer/Framework/Core/Stabilizer/StabilizerGroup.lean`]
- `mkStabilizerFromGenerators` — smart constructor for `StabilizerGroup`
  from a generator list. [same file]
- `Subgroup.closure` (Mathlib) — used directly in the `subgroup`
  definition. Standard mathlib API.
- `Subgroup.forall_comm_closure_iff` (Mathlib) — used in the
  centralizer-membership proofs. Standard mathlib API.

### CSS-side machinery
- `NQubitPauliGroupElement.IsZTypeElement`, `IsXTypeElement` — the CSS
  type predicates. [`QEC/Stabilizer/Framework/Core/CSS/CSSPredicates.lean`]
- `CSSCommutationLemmas.ZType_commutes`, `XType_commutes` — Z-type and
  X-type elements pairwise commute (trivial CSS fact).
  [`QEC/Stabilizer/Framework/Core/CSS/CSSCommutationLemmas.lean`]
- `CSS.negIdentity_not_mem_closure_union` — proves `−I ∉ subgroup` from
  Z-type, X-type, and cross-commutation data.
  [`QEC/Stabilizer/Framework/Core/CSS/CSSNoNegI.lean`]
- `NQubitPauliGroupElement.AllPhaseZero` (+ `AllPhaseZero_cons`,
  `AllPhaseZero_nil`) — phase-zero predicate on generator lists.
  [`QEC/Stabilizer/Foundations/PauliGroup/NQubitElement.lean`]
- `NQubitPauliGroupElement.rowsLinearIndependent` — symplectic check-
  matrix row independence; closed by `decide` for small n.
  [`QEC/Stabilizer/Foundations/BinarySymplectic/CheckMatrix.lean`]
- `GeneratorsIndependent`, `GeneratorsIndependent_of_rowsLinearIndependent`
  — bundled generator independence from `rowsLinearIndependent`.
  [`QEC/Stabilizer/Framework/Symplectic/IndependentEquiv.lean`]

### Commutation tactics
- `pauli_comm_componentwise` — closes `g * h = h * g` by per-qubit
  commutation table; works when supports are disjoint or both are
  Z-/X-type. [`QEC/Stabilizer/Foundations/PauliGroup/CommutationTactics.lean`]
- `pauli_comm_even_anticommutes` — reduces `g * h = h * g` to
  "the anticommuting-positions count is even"; used with an explicit
  filter Finset. [same file]
- `pauli_anticomm_odd_anticommutes` — reduces `Anticommute g h` to
  "the anticommuting-positions count is odd"; used with explicit
  Finset. [same file]
- `NQubitPauliGroupElement.anticommutesAt` — per-qubit anticommutation
  predicate used inside the filter Finset.
  [`QEC/Stabilizer/Foundations/PauliGroup/Commutation.lean`]
- `NQubitPauliGroupElement.Anticommute` — global anticommutation
  predicate (target of `pauli_anticomm_odd_anticommutes`).
  [same file]

### Logical-operator infrastructure
- `LogicalQubitOps n S` — bundle of (xOp, zOp, x_mem_centralizer,
  z_mem_centralizer, anticommute) per logical qubit.
  [`QEC/Stabilizer/Framework/Core/Logical/LogicalOperators.lean`]
- `StabilizerGroup.mem_centralizer_iff` — translates `g ∈ centralizer`
  to a forall-comm form. [`QEC/Stabilizer/Framework/Core/Stabilizer/Centralizer.lean`]
- `centralizer` (Subgroup-valued) — the centralizer of a stabilizer
  group inside the Pauli group. [same file]

### Code-level packaging
- `StabilizerCode n k` (structure) — bundled code with generator list +
  logical operators. [`QEC/Stabilizer/Framework/Core/Stabilizer/StabilizerCode.lean`]
- `StabilizerCode.toStabilizerGroup` — derived `StabilizerGroup` from
  the bundled code. [same file]
- `StabilizerCodeWithDistance n k d` — `StabilizerCode` + distance fact.
  [same file, around the end]

### Distance machinery
- `HasCodeDistance` — the distance predicate.
  [`QEC/Stabilizer/Framework/Core/Logical/CodeDistance.lean`]
- `hasCodeDistance_of` — general distance-from-witness schema.
  [same file]
- `IsNontrivialLogicalOperator`, `IsNontrivialLogicalOperator_iff`,
  `LogicalQubitOps.xOp_nontrivial` — the nontriviality predicates and
  their characterization. [`QEC/Stabilizer/Framework/Core/Logical/LogicalOperators.lean`]
- **`hasCodeDistance_two_of_anticommute_witness`** (PR #34) — proven,
  reusable distance-2 closer from `(genSet, h_closure,
  weight_one_anticomm_witness, weight_2 nontrivial logical)` ⟹
  `HasCodeDistance code 2`. Used by:
  - `Codes/Small/FourQubit_4_2_2.lean` (k=2 CSS detection)
  - `Codes/Small/CSS_4_1_2.lean` (k=1, multi-Z-stab CSS detection)
  - `Codes/Iceberg/N.lean` (parametric, full-support stabs)
  C_6 will be **the fourth user** — the first multi-Z-stab + k=2 user.
  [`QEC/Stabilizer/Framework/Core/CSS/CSSDistance.lean:165-179`]
- `no_weight_one_mem_centralizer_of_anticommute_witness` — the
  underlying helper that `hasCodeDistance_two_of_anticommute_witness`
  calls into. Provides the weight-1 anti-witness ⟹ no weight-1
  centralizer element. [same file:32-71]
- `weightOneAt` — the weight-1 Pauli group element constructor.
  [same file:26]

## Lightly adapted (existing pattern, new instance)

### From `Codes/Small/CSS_4_1_2.lean` (the closest multi-Z-stab CSS reference)
- **`ZGenerators_are_ZType` pattern**: extends 1 → 2 → 2 generators.
  C_6 uses 2 Z-stabs like CSS_4_1_2.
  - C_6 source: copy `CSS_4_1_2.ZGenerators_are_ZType` (lines 108-120)
    verbatim; rename `S_Z2 = IIZZ` (n=4) to `S_Z2 = ZZ II ZZ` (n=6).
- **`S_Z1_comm_S_X1` pattern (partial-support Z vs full-X)**:
  - C_6 source: similar to `CSS_4_1_2.S_Z1_comm_S_X1` (lines 139-149),
    but here every stab is partial-support, so all 4 cross-commute
    proofs use the same explicit-Finset pattern.
- **`weightOneAt_anticomm_S_Z1` pattern (sub-support helper)**:
  - C_6 source: copy CSS_4_1_2 lines 403-418 verbatim, extend the `hi`
    hypothesis from `i = 0 ∨ i = 1` (2-disjunction) to `i = 0 ∨ i = 1 ∨
    i = 2 ∨ i = 3` (4-disjunction; the support of `S_Z1` for n=6).
- **`hi_dichotomy` → `hi_trichotomy` pattern in
  `weight_one_anticomm_witness`**:
  - C_6 source: replace `hi_dichotomy : (i ∈ {0,1}) ∨ (i ∈ {2,3})` with
    a 3-disjunction. See gap_audit.md for details.

### From `Codes/Small/FourQubit_4_2_2.lean` (the closest k=2 CSS reference)
- **k=2 `LogicalQubitOps` packaging** (`logicalOps4_2_2`, lines 438-445):
  - C_6 source: copy verbatim, renaming the 4 logicals
    (`logicalX_1 = IIXXII`, etc.).
- **`logical_commute_cross := by fin_cases ...` proof** (lines 457-467):
  - C_6 source: copy verbatim. Same 4-case dispatch structure.
- **Off-diagonal logical commutation proofs (T17-T20)**:
  - C_6 source: copy `FourQubit_4_2_2.logicalX_1_commutes_logicalX_2`
    (line 278), `logicalX_1_commutes_logicalZ_2` (line 282-294),
    `logicalX_2_commutes_logicalZ_1` (line 297-309),
    `logicalZ_1_commutes_logicalZ_2` (line 313) as templates. Adjust the
    explicit Finsets per the new logical operator supports.
- **`logicalX_1_mem_centralizer` per-generator dispatch** (lines 384-394):
  - C_6 source: extends 1-Z + 1-X (2-case) to 2-Z + 2-X (4-case) by
    expanding the `rcases (by simpa [ZGenerators] using hgZ)` from
    `with rfl` to `with rfl | rfl`.
- **`code_has_distance_two` proof** (lines 534-537):
  - C_6 source: copy verbatim, swap in C_6's witness and weight-2
    logical witness.

### From `Codes/Small/CSS_4_1_2.lean` and `FourQubit_4_2_2.lean` (mixed)
- **`generatorsList`, `listToSet_generatorsList`** (`[Z1, Z2, X1, X2]`):
  - C_6 source: extend `CSS_4_1_2.generatorsList = [S_Z1, S_Z2, S_X1]`
    (3 elements) to `[S_Z1, S_Z2, S_X1, S_X2]` (4 elements).
- **`AllPhaseZero_generatorsList`** (chain of `⟨rfl, ...⟩`):
  - C_6 source: extend CSS_4_1_2's 3-level nesting to 4 levels.
- **`stabilizerGroup_toSubgroup_eq`** (line 259-262 of CSS_4_1_2):
  - C_6 source: copy verbatim.
- **`stabilizerCode_toSubgroup_eq`** (line 393-397 of CSS_4_1_2):
  - C_6 source: copy verbatim.

## New per-code definitions (no analog elsewhere)

These are genuinely C_6-specific and have no existing template:

- `Z1, Z2, X1, X2` — the four stabilizer Pauli strings as
  `NQubitPauliGroupElement 6`.
- `logicalX_1, logicalX_2, logicalZ_1, logicalZ_2` — the four logical
  operators per Knill 2004.
- The 16 specific Finset values (`{0,1,2,3}, {0,1}, {2,3}, ...`)
  appearing in the `pauli_comm_even_anticommutes` filters.
- The 4-disjunction hypotheses (`i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3` for
  qubits covered by `S_Z1` / `S_X1`; `i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5`
  for qubits covered by `S_Z2` / `S_X2`) used in the `weightOneAt_anticomm_*`
  helper lemmas.
- The 3-disjunction `hi_trichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3)
  ∨ (i = 4 ∨ i = 5)` used in `weight_one_anticomm_witness`.

These are pure data; no new tactic patterns or lemma APIs are added.

## Imports needed

Copy verbatim from `CSS_4_1_2.lean`'s import block (lines 1-19):
```
import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
```
All imports already exist; no new framework modules required.

## Umbrella import

Add the new file to `QEC/Stabilizer/Codes/Small.lean`:
```
import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2
```
The cluster umbrella (`QEC/Stabilizer/Codes/Small.lean`) already lists
the 7 existing small codes; we add the 8th. The transitive umbrella
chain to `Stabilizer.lean` is automatic.

## Conclusion

The C_6 formalization adds **0 new framework abstractions** and **0
new tactic patterns**. Every theorem is a direct adaptation of a
pattern proven in `CSS_4_1_2.lean` or `FourQubit_4_2_2.lean`. This is
the textbook "engineering track" case: the next-rank code on the
queue whose proof is mechanical and whose new content is purely data
(generators, logicals, Finsets).

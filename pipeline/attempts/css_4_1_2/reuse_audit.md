# Reuse audit: [[4,1,2]] LNCY code

This code is exceptionally close in structure to `FourQubit_4_2_2.lean`
(same `n = 4`, same CSS detection structure, same distance proof method)
and `Steane7.lean` (canonical `k = 1` CSS instantiation). Reuse is
correspondingly very high.

## Directly applicable (use as-is)

### Core types and structures
- `NQubitPauliGroupElement 4` — physical Pauli group on 4 qubits
  (`QEC/Stabilizer/Foundations/PauliGroup/NQubitElement.lean`)
- `NQubitPauliOperator.identity 4` — the all-`I` operator
- `NQubitPauliOperator.set i P` — set qubit `i` to local Pauli `P`
- `Subgroup.closure`, `StabilizerGroup 4`, `mkStabilizerFromGenerators`
- `IsXTypeElement`, `IsZTypeElement` from
  `Framework/Core/CSS/CSSPredicates.lean`
- `LogicalQubitOps 4 stabilizerGroup` — bundled logical-qubit data
  (`Framework/Core/Logical/LogicalOperators.lean:189`)
- `StabilizerCode 4 1`, `StabilizerCodeWithDistance 4 1 2`
  (`Framework/Core/Stabilizer/StabilizerCode.lean`,
  `Framework/Core/Logical/CodeDistance.lean:81`)
- `HasCodeDistance` predicate
  (`Framework/Core/Logical/CodeDistance.lean:28`)
- `centralizer`, `StabilizerGroup.mem_centralizer_iff`,
  `Subgroup.forall_comm_closure_iff`
  (`Framework/Core/Stabilizer/Centralizer.lean`)

### CSS shortcuts (all directly applicable — this is a CSS code)
- `CSS.negIdentity_not_mem_closure_union`
  (`Framework/Core/CSS/CSSNoNegI.lean`) — closes `-I ∉ closure(Z ∪ X)`
  given the type predicates and the cross-commutation hypothesis.
- `CSSCommutationLemmas.ZType_commutes` and `XType_commutes`
  (`Framework/Core/CSS/CSSCommutationLemmas.lean`) — two Z-type
  elements always commute, same for X-type.
- `weightOneAt`, `no_weight_one_mem_centralizer_of_anticommute_witness`
  (`Framework/Core/CSS/CSSDistance.lean:25`, `:31`) — the distance proof
  is one application of this lemma + a weight-1 anti-witness function
  (T19).

### Tactics
- `pauli_comm_componentwise [...]` — closes `g * h = h * g` when no
  two qubits anticommute (e.g. both Z-type)
  (`Foundations/PauliGroup/CommutationTactics.lean:36`).
- `pauli_comm_even_anticommutes` — converts `g * h = h * g` to an
  "even number of anticommuting qubits" goal
  (`Foundations/PauliGroup/CommutationTactics.lean:54`).
- `pauli_anticomm_odd_anticommutes` — same for `Anticommute g h`
  (`Foundations/PauliGroup/CommutationTactics.lean:66`).

### Independence machinery
- `rowsLinearIndependent` (decidable on small n)
  (`Foundations/BinarySymplectic/CheckMatrixDecidable.lean`)
- `GeneratorsIndependent_of_rowsLinearIndependent`
  (`Framework/Symplectic/IndependentEquiv.lean`)
- `AllPhaseZero_cons`, `AllPhaseZero_nil`
  (`Foundations/PauliGroup/NQubitElement.lean`)

### Helpers used in the distance proof
- `hasCodeDistance_of`
  (`Framework/Core/Logical/CodeDistance.lean:54`)
- `IsNontrivialLogicalOperator_iff`
  (`Framework/Core/Logical/LogicalOperators.lean:176`)
- `LogicalQubitOps.xOp_nontrivial`
  (`Framework/Core/Logical/LogicalOperators.lean:326`)

## Lightly adapted (existing pattern, new instance)

### Top-level file structure
Mirror `FourQubit_4_2_2.lean` (`Codes/Small/FourQubit_4_2_2.lean`) at
the section level (§1 generators → §14 distance). The differences:

- **§1 (generators)**: `[[4,2,2]]` has `{ZZZZ, XXXX}`; LNCY has
  `{ZZII, IIZZ, XXXX}`. Add one extra Z-generator definition (`S_Z2`).
- **§3, §4 (typing/cross-commutation)**: 2×1 = 2 cross pairs instead
  of 1×1 = 1. Pattern unchanged, just one more lemma.
- **§9 (independence)**: `decide` runs on a 3-row matrix instead of
  2-row. Still trivially decidable.
- **§10–§13 (logicals)**: only one logical qubit (`logicalX`,
  `logicalZ`) instead of two; the `Subsingleton.elim` shortcut from
  `Steane7.lean:510` discharges `logical_commute_cross`. Pattern from
  Steane7, not [[4,2,2]].
- **§14 (distance)**: T19's anti-witness function dispatches over
  which Z-generator to use (`S_Z1` for `i ∈ {0, 1}`, `S_Z2` for
  `i ∈ {2, 3}`). [[4,2,2]] had only one Z-generator so no such split.

### Specific copy-paste sites (with adaptation)
- **`Z1`, `Z2` (`S_Z1`, `S_Z2`)**: adapt from `Steane7.lean:49-65`
  (per-qubit `.set` chain) for support `{0, 1}` and `{2, 3}`
  respectively.
- **`X1` (`S_X1 = XXXX`)**: directly reuse the definition from
  `FourQubit_4_2_2.lean:64` (`XXXX`).
- **`ZGenerators`, `XGenerators`, `generators`,
  `subgroup`**: `Steane7.lean:85-98` pattern.
- **`ZGenerators_are_ZType`**: `Steane7.lean:105` pattern for 2 Z
  generators (rcases with `rfl | rfl`).
- **`XGenerators_are_XType`**: `FourQubit_4_2_2.lean:99` pattern (1 X
  generator).
- **Cross-commutation `S_Z1_comm_S_X1`, `S_Z2_comm_S_X1`**: copy
  `FourQubit_4_2_2.Z1_comm_X1` (line 114), adjusting `Finset` for
  `{0, 1}` and `{2, 3}`.
- **`ZGenerators_commute_XGenerators`**:
  `Steane7.lean:227` pattern (2×1 cases instead of 3×3).
- **`generators_commute`**, **`negIdentity_not_mem`**,
  **`generatorsList`**, **`listToSet_generatorsList`**: all
  line-for-line analogs of `FourQubit_4_2_2.lean:149`, `:165`, `:175`,
  `:179`.
- **`AllPhaseZero_generatorsList`**: nested `⟨rfl, ...⟩` for 3
  elements (extend `FourQubit_4_2_2.lean:188` from 2 to 3).
- **`rowsLinearIndependent_generatorsList`,
  `GeneratorsIndependent_4_generatorsList`**: copy
  `FourQubit_4_2_2.lean:195-202`.
- **`stabilizerGroup`, `stabilizerGroup_toSubgroup_eq`**: copy
  `FourQubit_4_2_2.lean:207-215`.
- **`logicalX`, `logicalZ`**: define directly (`XXII` and `ZIZI` per
  the spec). Use the `.set` pattern from `FourQubit_4_2_2.lean:227-240`.
- **`logicalX_anticommutes_logicalZ`**: `FourQubit_4_2_2.lean:245`
  pattern with filter `{0}` (size 1).
- **Per-generator logical-commutation lemmas
  (`logicalX_commutes_S_Z1` etc.)**: 6 lemmas total (2 logicals × 3
  generators). Each follows `FourQubit_4_2_2.lean:318` or
  `:331` (`pauli_comm_componentwise` for same-type-type commute,
  `pauli_comm_even_anticommutes` + Finset for cross-type commute).
- **`logicalX_mem_centralizer`, `logicalZ_mem_centralizer`**:
  `FourQubit_4_2_2.lean:384-407` pattern, simplified to one logical
  per centralizer (no k = 2 partitioning).
- **`stabilizerCode`, `logicalOps`**:
  `Steane7.lean:496-510` pattern (k = 1 case with
  `Subsingleton.elim` cross-commute).
- **`stabilizerCode_toSubgroup_eq`**: `FourQubit_4_2_2.lean:472`
  pattern (private bridge lemma).
- **`weightOneAt_anticomm_S_Z`, `weightOneAt_Z_anticomm_S_X1`**:
  adapt `FourQubit_4_2_2.lean:480` and `:499` patterns; the Z-side
  helper needs an extra parameter for which Z-generator (or two
  separate lemmas: one for `S_Z1`, one for `S_Z2`).
- **`weight_one_anticomm_witness`**: `FourQubit_4_2_2.lean:517`
  pattern, with an inner `fin_cases i` to dispatch between `S_Z1`
  and `S_Z2`.
- **`code_has_distance_two`**: `FourQubit_4_2_2.lean:534` pattern.
- **`stabilizerCodeWithDistance`**: `FourQubit_4_2_2.lean:546` pattern.

## New per-code definitions

Nothing genuinely new — every definition has a 1-to-1 analog in
`FourQubit_4_2_2.lean` or `Steane7.lean`. The only structural novelty
is the 2-Z + 1-X split (everything else in the repo has either
balanced splits or single-generator splits per Pauli type), but no
new abstraction is required to express it.

## Umbrella file update

Add the new module to the `Codes/Small.lean` umbrella:
`QEC/Stabilizer/Codes/Small.lean` currently imports 6 small codes
(`Shor9`, `Steane7`, `Steane7TransversalGates`, `FourQubit_4_2_2`,
`QuantumHamming`, `FiveQubit_5_1_3`). Append:
```
import QEC.Stabilizer.Codes.Small.CSS_4_1_2
```
and update the doc comment to mention the LNCY [[4,1,2]] code.

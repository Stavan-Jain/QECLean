# Reuse audit: \([[5,1,3]]\) Five-qubit perfect code

## Directly applicable (use as-is)

### From `QEC/Stabilizer/PauliGroup/`

- `NQubitPauliGroupElement n` — 5-qubit Pauli group elements with
  phasePower : Fin 4 and operators : NQubitPauliOperator n
  (`PauliGroup/NQubitElement.lean`)
- `NQubitPauliOperator.identity 5` — the all-I operator base, used in
  every generator definition (`PauliGroup/NQubitOperator.lean:37`)
- `NQubitPauliOperator.set` — per-qubit Pauli assignment, used to
  chain `.set i PauliOperator.X` etc. when building generators
  (`PauliGroup/NQubitOperator.lean:56`)
- `NQubitPauliOperator.X n`, `.Y n`, `.Z n` — all-X / all-Y / all-Z
  operators (`PauliGroup/NQubitOperator.lean:41-50`). `logicalX` and
  `logicalZ` use `.X 5` and `.Z 5`.
- `NQubitPauliGroupElement.anticommutesAt` — per-qubit anticommutation
  predicate, fed into `Finset.univ.filter` for the
  `pauli_comm_even_anticommutes` residual goal
- `NQubitPauliGroupElement.Anticommute` — global anticommutation, used
  for `logicalX_anticommutes_logicalZ`
- `pauli_comm_even_anticommutes` tactic
  (`PauliGroup/CommutationTactics.lean`) — converts commutation goals
  into "even cardinality of anti-positions" goals. Used in 6 pairwise
  + 8 logical-vs-generator lemmas (14 sites total).
- `pauli_comm_componentwise` tactic — works for the
  logicalX/logicalZ trivial commutation cases, but those don't arise
  here (every logical-vs-generator pair has non-trivial overlap).
- `NQubitPauliOperator.allX_allZ_anticommute (n : ℕ) (h : Odd n)`
  (`BinarySymplectic/SymplecticInner.lean:106`) — closes
  `logicalX_anticommutes_logicalZ` in one line with `(by decide : Odd 5)`.

### From `QEC/Stabilizer/Core/`

- `StabilizerGroup n`, `.toSubgroup`, `.is_abelian`,
  `.no_neg_identity` (`Core/StabilizerGroup.lean:107`) — target
  structure for §8
- `negIdentity n`, `negIdentity_phasePower`, `negIdentity_operators`,
  `negIdentity_ne_one` (`Core/StabilizerGroup.lean:54-71`) — needed in §6
- `StabilizerGroup.mem_centralizer_iff` /
  `centralizer.mem_centralizer_iff` — for the centralizer-as-forall
  unfolding in §12
- `Subgroup.forall_comm_closure_iff`
  (`Core/SubgroupLemmas.lean:50`) — reduces "g commutes with every
  element of a closure" to "g commutes with every generator", used in
  `logicalX_mem_centralizer` / `logicalZ_mem_centralizer`
- `mkStabilizerFromGenerators` (`Core/StabilizerCode.lean:62`) — §8
  packaging
- `StabilizerCode` structure + `StabilizerCode.toStabilizerGroup`
  (`Core/StabilizerCode.lean:80, 110`) — §13 packaging
- `LogicalQubitOps` structure (`Core/LogicalOperators.lean:189`) — §13
  field `logicalOps`
- `IsNontrivialLogicalOperator`, `IsNontrivialLogicalOperator_iff`
  (`Core/LogicalOperators.lean:172-178`) — used in §14 distance proof
- `HasCodeDistance`, `hasCodeDistance_of`
  (`Core/CodeDistance.lean:28, 54`) — target / introduction lemma
  for §14
- `no_weight_one_mem_centralizer_of_anticommute_witness`
  (`Core/CSSDistance.lean:31`) — used in the weight-1 sub-case of §14
  (lemma name has "CSS" prefix but is **fully general** — works for
  non-CSS codes too)
- `weightOneAt (i : Fin n) (P : PauliOperator)`
  (`Core/CSSDistance.lean:25`) — single-qubit-supported Pauli, used
  in the weight-1 anti-witness construction

### From `QEC/Stabilizer/BinarySymplectic/`

- `NQubitPauliGroupElement.AllPhaseZero` and its `_cons` / `_nil`
  lemmas (`BinarySymplectic/IndependentEquiv.lean:45, 88, 98`) —
  used to chain phase-0 proofs for `generatorsList`
- `NQubitPauliGroupElement.rowsLinearIndependent`
  (`BinarySymplectic/CheckMatrix.lean`) — independence via
  symplectic check matrix
- `GeneratorsIndependent_of_rowsLinearIndependent`
  (`Core/StabilizerCode.lean:48`) — bridges check-matrix
  independence to `GeneratorsIndependent`
- `NQubitPauliGroupElement.listToSet`,
  `listToSet_cons`, `listToSet_nil`
  (`BinarySymplectic/IndependentEquiv.lean:41, 70, 77`) — Set ↔ List
  bridge for the generator list

## Lightly adapted (existing pattern, new instance)

These are patterns from sibling code files that we copy/instantiate
verbatim, just renaming and changing `n`:

- **Per-pair commutation lemmas** — pattern from
  `Steane7.lean:136-224` (the nine `Zᵢ_comm_Xⱼ` lemmas). Adapt for the
  six g_i_comm_g_j unordered pairs.
- **`logicalX_commutes_gᵢ` / `logicalZ_commutes_gᵢ` lemmas** —
  pattern from `Steane7.lean:364-474`. Adapt for n = 5 and the four
  cyclic-shift generators.
- **`logicalX_mem_centralizer` / `logicalZ_mem_centralizer`** —
  pattern from `Steane7.lean:413-426` and `Steane7.lean:477-490`.
- **`generatorsList`, `listToSet_generatorsList`,
  `AllPhaseZero_generatorsList`** — pattern from
  `Steane7.lean:286-327`, scaled to 4 generators.
- **`rowsLinearIndependent_generatorsList`,
  `GeneratorsIndependent_5_generatorsList`** — pattern from
  `Steane7.lean:330-336`.
- **`stabilizerGroup`, `stabilizerGroup_toSubgroup_eq`** — pattern
  from `Steane7.lean:301-309`.
- **`stabilizerCode`** — pattern from `Steane7.lean:496-510` (k = 1,
  `Subsingleton.elim` shortcut for `logical_commute_cross`).
- **`weight_one_anticomm_witness` and `weightOneAt_anticomm_*` helpers**
  — pattern from `FourQubit_4_2_2.lean:478-543`. Adapt for n = 5 and
  the four generators; need 4 helper lemmas (one per single-qubit
  Pauli class) and one `weight_one_anticomm_witness` aggregator.
- **`stabilizerCode_toSubgroup_eq` bridge lemma** — pattern from
  `FourQubit_4_2_2.lean:472-476`, needed for the distance proof's
  centralizer-closure step.

## New per-code definitions

These have no analog in the repo; they are introduced for the
five-qubit code:

- **Generator defs** `g1, g2, g3, g4 : NQubitPauliGroupElement 5` —
  the four cyclic-shift `XZZXI` Paulis. Naming follows
  `FourQubit_4_2_2`'s `Z1`/`X1` convention, but since there's no Z/X
  split, we use plain `g1..g4` (alternative: `XZZXI_0`, `XZZXI_1`,
  ... matching the EC Zoo tableau row order — discuss in Stage 3).
- **Logicals** `logicalX, logicalZ : NQubitPauliGroupElement 5` —
  all-X / all-Z, same shape as Steane7's but for n = 5.
- **`logicalX_weight3 : NQubitPauliGroupElement 5`** — the weight-3
  representative `logicalX * g₁` (phase 2, operators IYYIX). Used as
  the distance witness in §14. **This is the central new construction
  and the main Stage-3 review point.**
- **`weight_two_anticomm_witness`** — if the manual weight-2
  enumeration path is taken, this aggregator lemma is new (no
  analog in `FourQubit_4_2_2.lean` because [[4,2,2]] has d = 2 and
  only needs the weight-1 sub-case).

## Patterns from CSS code that we explicitly DO NOT use

- **`ZGenerators` / `XGenerators` set partition** (Steane7:85-94,
  FourQubit_4_2_2:70-79) — no Z/X split for non-CSS.
- **`ZGenerators_are_ZType` / `XGenerators_are_XType`** typing lemmas
  (Steane7:105-128) — `IsZTypeElement` / `IsXTypeElement` predicates
  fail on every five-qubit-code generator since they contain mixed
  X and Z factors.
- **`ZGenerators_commute_XGenerators`** — no Z/X partition, so this
  packaging step is replaced by pairwise commutation across all 6
  unordered pairs of generators (which subsumes it).
- **`ZType_commutes`, `XType_commutes`** (Steane7:247-257) — same
  rationale.
- **`CSS.negIdentity_not_mem_closure_union`** — see `gap_audit.md`:
  this is the largest reuse gap. We need a general-form replacement.

## Summary: lines of code from each reuse category

| Category | Approx LoC | Source |
|----------|-----------:|--------|
| Generator + set definitions | 30 | new per-code |
| Per-pair commutation (6 lemmas) | 50 | pattern from Steane7 |
| `generators_commute` top-level | 25 | adapted (no CSS shortcut) |
| `negIdentity_not_mem` | 10 + 40 in `SubgroupLemmas.lean` | **new general lemma** |
| Generator list + listToSet | 12 | Steane7 pattern |
| AllPhaseZero + independence | 12 | Steane7 pattern |
| stabilizerGroup + bridge | 12 | Steane7 pattern |
| Logical operators + anticommute | 12 | Steane7 pattern |
| logicalX/Z × g_i commutations (8 lemmas) | 70 | Steane7 pattern |
| logicalX_mem_centralizer + logicalZ_mem_centralizer | 30 | Steane7 pattern |
| stabilizerCode packaging | 15 | Steane7 pattern |
| Distance: `native_decide` attempt | 3 | new |
| Distance: weight-1 manual enumeration | 50 | FourQubit_4_2_2 pattern |
| Distance: weight-2 manual enumeration | 100 + 40 in `CSSDistance.lean` | **new general lemma** |
| Distance: witness construction (`logicalX_weight3`) | 30 | new |
| **Total estimate** | **~650 LoC** (incl. ~80 LoC in core lemmas) | |

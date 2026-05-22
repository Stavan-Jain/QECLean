# Formalization plan: \([[5,1,3]]\) Five-qubit perfect code

## Strategy summary

Follow the standard `_TEMPLATE.lean` §1–§14 layout, scaled to `n = 5`,
`k = 1`, `d = 3`, but with the non-CSS divergences flagged in
`informal_spec.md`. The 6 pairwise commutations + 8 logical-vs-generator
commutations are all closed by `pauli_comm_even_anticommutes` with
explicit anticommute-Finset computation (mirroring Steane7's
`Zᵢ_comm_Xⱼ` pattern). The `−I ∉ closure` step routes through a new
general-purpose lemma in `Core/SubgroupLemmas.lean` (or a local
ad-hoc proof). The distance proof preferentially tries `native_decide`
on the full `HasCodeDistance` predicate; failing that, falls back to
manual enumeration via `no_weight_{one,two}_mem_centralizer_of_*`
helpers (the weight-2 helper does not yet exist in the repo).

## Theorem dependency graph

```
T_pair_ij (6 leaves)         T_logX_vs_gᵢ (4 leaves)
        \                     /                \
         \                   /                  \
    generators_commute       \              T_logZ_vs_gᵢ (4 leaves)
            |                 \                 |
            |                  \                |
    AllPhaseZero_list       logicalX_mem_       logicalZ_mem_
    rowsLinIndep_list       centralizer         centralizer
            |   |                 \            /
            |   |                  \          /
            |   |                   \        /
            |   |  negIdentity_      logical-anticommute (allX_allZ)
            |   |  not_mem               |
            |   |       \                |
            |   v        v               v
            |  stabilizerGroup -----> LogicalQubitOps
            |       |                       |
            |       v                       |
            |  stabilizerCode <-------------+
            |       |
            v       v
       HasCodeDistance (uses anti-witness helpers + weight-3 witness)
```

(Indentation = depth in the proof DAG; arrows = used-by.)

## Per-theorem proof sketch

### §1: Generator definitions (T_def_g1..4)
- Approach: copy Steane7's pattern. Four `def gᵢ : NQubitPauliGroupElement 5`
  using `⟨0, (((identity 5).set ...).set ...)⟩`.
- Existing lemmas: none needed.
- Difficulty: trivial.

### §2: Generator set & subgroup (T_def_generators, T_def_subgroup)
- Approach: `def generators : Set (NQubitPauliGroupElement 5) := {g₁, g₂, g₃, g₄}`
  (no Z/X partition — non-CSS!).
- `noncomputable def subgroup := Subgroup.closure generators`.
- Difficulty: trivial.

### §4: Per-pair commutation (T1: 6 lemmas g_i_comm_g_j)
- Approach: `pauli_comm_even_anticommutes` + explicit Finset computation,
  identical shape to `Zᵢ_comm_Xⱼ` in Steane7. Each lemma is ~7 lines.
- Existing lemmas:
  - `pauli_comm_even_anticommutes` tactic (`PauliGroup/CommutationTactics.lean`)
  - `NQubitPauliGroupElement.anticommutesAt`
- Anti-position Finsets (from `informal_spec.md`):
  ```
  g1_g2: {1,3}    g1_g3: {2,3}    g1_g4: {0,1}
  g2_g3: {2,4}    g2_g4: {3,4}    g3_g4: {0,3}
  ```
- Difficulty: standard. 6 × ~7 lines ≈ 42 LoC.

### §5: All-pair commutation (T_generators_commute)
- Approach: `rcases hg with rfl | rfl | rfl | rfl` × `rcases hh with ...`
  (16 cases), each closed by one of the 6 `g_i_comm_g_j` lemmas (or
  trivially when `g = h`). Cannot use CSS shortcuts (no Z/X partition).
- Existing lemmas: only the per-pair lemmas above.
- Difficulty: mechanical case-bash. ~30 LoC.

### §6: −I not in stabilizer (T2: negIdentity_not_mem)
- Approach: **new path — general non-CSS form.** Two options:
  1. **Preferred**: add `negIdentity_not_mem_of_independent_phase_zero`
     to `Core/SubgroupLemmas.lean` and call it. Proof sketch:
     - Hypothesis: `AllPhaseZero L`, `GeneratorsIndependent n L`.
     - Suppose for contradiction `negIdentity n ∈ Subgroup.closure (listToSet L)`.
     - `negIdentity n` has `phasePower = 2` and `operators = identity n`.
     - Any element of the closure factors as `g = ∏ gᵢ^aᵢ` with
       `aᵢ ∈ {0,1}` (because each gᵢ is order ≤ 2 after squaring,
       which gives `gᵢ² = ±1`; phase-0 ⇒ `gᵢ² = 1` ⇒ subgroup is
       elementary abelian).
     - Wait — `gᵢ²` for `gᵢ` phase-0 with operators `O` has phase
       `(O·O).phase` which is 0 only if `O` is its own inverse with no
       phase, i.e. `O² = identity` in the operator sense. For Paulis,
       any Pauli squared (as operator) is identity, so `gᵢ²` has phase
       0 and operator identity, hence `gᵢ² = 1`. ✓
     - So closure is `{0, 1}`-linear combinations of generators.
       Operator part is `Σ aᵢ · symplectic(gᵢ)` (mod 2). For this to
       equal `identity` (symplectic vector 0), linear independence of
       rows forces all `aᵢ = 0`, hence the product is `1`, not
       `negIdentity`.
     - Conclude `−I = 1`, contradicting `negIdentity_ne_one n`.
  2. **Fallback**: inline this argument in the code file.
- Existing lemmas needed for option 1:
  - `mem_closure_implies_symp_in_span` (Stage 1 of the argument)
  - `negIdentity_phasePower`, `negIdentity_operators`, `negIdentity_ne_one`
  - `rowsLinearIndependent` ⇒ `IndependentGenerators`
  - A new "elementary abelian closure" lemma for phase-0 Paulis (may
    already exist; check `BinarySymplectic/SymplecticSpan.lean`).
- Difficulty: **novel for this repo** (~30-50 LoC in a new core lemma,
  plus ~5 LoC at the call site). Flagged in `gap_audit.md`.

### §7: Generator list & `listToSet` (T_generatorsList, T_listToSet_eq)
- Approach: `def generatorsList : List (NQubitPauliGroupElement 5) := [g₁, g₂, g₃, g₄]`.
- `listToSet_generatorsList` proof identical pattern to Steane7 (5 lines).
- Difficulty: trivial.

### §9: AllPhaseZero + independence (T3, T4)
- Approach: `AllPhaseZero_generatorsList` is a chain of
  `(AllPhaseZero_cons _ _).mpr ⟨rfl, ...⟩` — 4 nestings deep
  (4 generators).
- `rowsLinearIndependent_generatorsList` closes by `decide`. For n=5
  and 4 rows, decision should be fast.
- `GeneratorsIndependent_5_generatorsList` is one-liner
  `GeneratorsIndependent_of_rowsLinearIndependent 5 generatorsList _`.
- Difficulty: trivial. ~12 LoC.

### §8: StabilizerGroup packaging (T7)
- Approach: copy Steane7's `mkStabilizerFromGenerators 5 generatorsList ... ...`
  with the two hypotheses from above.
- `stabilizerGroup_toSubgroup_eq : stabilizerGroup.toSubgroup = subgroup`
  also one-liner.
- Difficulty: trivial. ~10 LoC.

### §10: Logical operators (T_logicalX, T_logicalZ)
- Approach: `def logicalX := ⟨0, NQubitPauliOperator.X 5⟩` and similar
  for `logicalZ`. Same as Steane7.
- Difficulty: trivial.

### §11: Logical anticommutation (T5: logicalX_anticommutes_logicalZ)
- Approach: `NQubitPauliOperator.allX_allZ_anticommute 5 (by decide : Odd 5)`.
  One line.
- Difficulty: trivial.

### §12: Logicals in centralizer (T6: logicalX_mem_centralizer + logicalZ_mem_centralizer)
- Approach: 8 per-generator lemmas (`logicalX_commutes_gᵢ` for i=1..4
  and `logicalZ_commutes_gᵢ` for i=1..4), each via
  `pauli_comm_even_anticommutes` + Finset computation. Then bundle via
  `Subgroup.forall_comm_closure_iff` exactly as Steane7.
- Anti-position Finsets:
  ```
  logicalX×g1: {1,2}    logicalX×g2: {2,3}    logicalX×g3: {3,4}    logicalX×g4: {0,4}
  logicalZ×g1: {0,3}    logicalZ×g2: {1,4}    logicalZ×g3: {0,2}    logicalZ×g4: {1,3}
  ```
- Existing lemmas: same as §4.
- Difficulty: standard. 8 × ~8 lines + ~15 LoC for centralizer bundling
  ≈ 80 LoC.

### §13: StabilizerCode packaging (T8: stabilizerCode)
- Approach: copy Steane7's pattern. `Fin 1 → LogicalQubitOps 5 stabilizerGroup`
  via the constant function returning the X/Z pair. `logical_commute_cross`
  by `Subsingleton.elim`.
- Difficulty: trivial. ~15 LoC.

### §14: Distance proof (T9: code_has_distance_three)

**Try `native_decide` first**:

```lean
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 := by
  native_decide
```

For `n = 5`, the universe of n-qubit Pauli group elements is `4 × 4^5 =
4096`. The `IsNontrivialLogicalOperator` predicate involves a forall
over the 16-element stabilizer subgroup and a forall over the 5
generators (for the centralizer check). Total decision tree:
4096 × 16 × 4 ≈ 262k operations — well within `native_decide` range.

**If `native_decide` fails or is too slow**:

Manual enumeration via `hasCodeDistance_of`:

1. `d ≥ 1`: `by decide`.

2. **Witness**: need a weight-3 non-trivial logical.
   - Define `logicalX_weight3 := logicalX * g₁` (phase 2, operator
     `IYYIX`, weight 3).
   - Or define it directly as
     `⟨2, ((identity 5).set 1 Y).set 2 Y |>.set 4 X⟩` and prove
     equality with `logicalX * g₁` separately if needed.
   - Show it's non-trivial: use a "mul by stabilizer preserves
     non-triviality" lemma. Either it exists already (search
     `LogicalOperatorCoset.lean`) or we add it:
     ```lean
     lemma IsNontrivialLogicalOperator_mul_mem_subgroup
       {S : StabilizerGroup n} {g : NQubitPauliGroupElement n}
       (hg : IsNontrivialLogicalOperator g S)
       (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup) :
         IsNontrivialLogicalOperator (g * s) S
     ```
     Three sub-proofs: centralizer-closed under right-multiplication
     by stabilizer; `g * s ∉ S` since `g ∉ S`; operator-part
     condition: for any `s' ∈ S`, `s'.operators ≠ (g*s).operators`
     because if `s'.operators = (g*s).operators`, then
     `(s' * s⁻¹).operators = g.operators` and `s' * s⁻¹ ∈ S`, but the
     original hypothesis says no `s'' ∈ S` has `s''.operators =
     g.operators`. Contradiction.
   - Weight 3 by `by decide` (or `simp [weight, ...]` + arithmetic).

3. **Lower bound** `∀ w, 1 ≤ w < 3, ∀ g, weight g = w →
   ¬IsNontrivialLogicalOperator g stabilizerCode.toStabilizerGroup`:
   - **Weight 1**: use
     `no_weight_one_mem_centralizer_of_anticommute_witness` (already
     in repo). Provide the witness function:
     ```lean
     ∀ i : Fin 5, ∀ P : PauliOperator, P ≠ I →
       ∃ g ∈ generators, Anticommute (weightOneAt i P) g
     ```
     Closed by a `fin_cases i <;> cases P <;>` that picks the right
     gᵢ per the table in `informal_spec.md`. ~30 LoC.

   - **Weight 2**: requires the **new repo lemma**
     `no_weight_two_mem_centralizer_of_anticommute_witness` (see
     `gap_audit.md`). The witness function:
     ```lean
     ∀ i j : Fin 5, i ≠ j → ∀ P Q : PauliOperator, P ≠ I → Q ≠ I →
       ∃ g ∈ generators, Anticommute (weightTwoAt i j P Q) g
     ```
     ~90 case-bash sites (10 unordered pairs × 9 (P, Q) combos),
     each closed by picking the gⱼ that anticommutes with the
     resulting two-qubit Pauli at the relevant positions. ~80-120 LoC.

   - **Or**, after closing the weight-1 case, attempt `native_decide`
     on just the weight-2 case; if that works, skip the manual
     enumeration.

- Difficulty: **uncertain — the largest risk in the whole proof.**
  The fallback path (manual weight-2 enumeration with a new helper
  lemma) is ~150 LoC of routine but tedious case-bash. The optimistic
  path (`native_decide` on full `HasCodeDistance`) closes everything
  in a few lines.

## Risk register

| Risk | Severity | Mitigation |
|------|----------|------------|
| `native_decide` on full distance times out for n=5 | medium | Manual enumeration path documented above; CSSDistance.no_weight_one_* helper already exists; only weight-2 helper is new. |
| No general `negIdentity_not_mem_of_independent_phase_zero` lemma exists | **high — first non-CSS code** | Add it to `Core/SubgroupLemmas.lean` as a Stage-4 prerequisite. Proof outline given above. |
| Weight-3 witness construction (`logicalX * g₁`) — non-triviality proof | medium | Add `IsNontrivialLogicalOperator_mul_mem_subgroup` helper if not present; check `LogicalOperatorCoset.lean` first. |
| `pauli_comm_even_anticommutes` `Finset` computation for residual goal may not reduce cleanly under `decide` for n=5 | low | Used identically for n=4 and n=7 in existing code; n=5 should be no different. |
| `rowsLinearIndependent_generatorsList` `by decide` is too slow | low | Fall back to `native_decide`. 4 rows × 10 columns is tiny. |
| `simp [g₁, ..., NQubitPauliOperator.set, ...]` doesn't fully reduce after `fin_cases i` | low | The existing Steane7 / FourQubit_4_2_2 patterns work for the same shape; if a particular position is stuck, add the `PauliOperator.mulOp` rewrite explicitly. |

## Estimated effort

- **Total LoC for the .lean file** (skeleton + sorries): ~250 LoC.
- **Total LoC after Stage 4 (all sorries closed)**: ~650 LoC.
  (Compare: Steane7 = 515 LoC, FourQubit_4_2_2 = 547 LoC. The
  five-qubit code has 6 pairwise commutations + 8 logical-vs-generator
  commutations + weight-1 and weight-2 distance enumerations, which
  is slightly more than Steane7 but less than FourQubit_4_2_2.)
- **Estimated proof attempts on the hardest theorem**: 5-10 attempts on
  the distance proof (`native_decide` vs manual enumeration vs
  hybrid). Other theorems should close on the first 1-2 attempts each
  by pattern-matching against Steane7.
- **Wall-clock estimate for Stage 4**: 1-2 sessions of ~4 hours each,
  dominated by (a) writing/closing the new `negIdentity_not_mem_of_*`
  general lemma in `Core/SubgroupLemmas.lean` and (b) the distance
  proof (especially if `native_decide` times out).

## Order to attempt theorems in Stage 4

1. Generator definitions and `listToSet_generatorsList` (warm-up).
2. `AllPhaseZero_generatorsList` and `rowsLinearIndependent_generatorsList`
   (both should close by `decide` / chained `cons.mpr ⟨rfl, ...⟩`).
3. The 6 per-pair commutation lemmas (template-driven).
4. `generators_commute` top-level (case-bash on the 4-element generator
   set).
5. **`negIdentity_not_mem`** — likely requires adding a new helper to
   `Core/SubgroupLemmas.lean` first. Pivot to general lemma if
   inline proof gets >50 LoC.
6. `stabilizerGroup` + bridge lemmas.
7. Logical operators + `logicalX_anticommutes_logicalZ`.
8. 8 logical-vs-generator commutations.
9. `logicalX_mem_centralizer` and `logicalZ_mem_centralizer`.
10. `stabilizerCode` packaging.
11. **Distance proof** — start with `native_decide`; if it works, ship
    it. Otherwise switch to manual enumeration with the weight-1 and
    weight-2 helpers.

## What this code does NOT need

- No `CSSPredicates` (`IsZTypeElement`, `IsXTypeElement`) — non-CSS.
- No `CSSCommutationLemmas` (`ZType_commutes`, `XType_commutes`) —
  no Z/X partition.
- No `CSSNoNegI.negIdentity_not_mem_closure_union` — see §6 above.
- No homological / lattice imports — small finite code.
- No trimmed-generator-list packaging — there are exactly `n − k = 4`
  generators, already independent.

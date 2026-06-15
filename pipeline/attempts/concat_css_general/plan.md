# Formalization plan: CSS code concatenation `[[n₁·n₂, k₂, ≥ d₁·d₂]]`

> **Status: plan only.** No Lean has been written. Signatures below are
> design-level proposals for Stage 2, not verified code. Produced 2026-06-15
> via a grounding → design → adversarial-critique → synthesis workflow.

## Strategy summary

Concatenate an inner CSS `[[n₁,1,d₁]]` with an outer CSS `[[n₂,k₂,d₂]]` into a
CSS `[[n₁·n₂, k₂, ≥ d₁·d₂]]`. Three structural tiers plus a gating framework
theorem and a concrete instance:

- **Tier 0 (M1):** operator embedding/reindexing calculus — the missing
  primitive (no embed/tensor/relabel of Paulis across qubit counts exists today).
- **Tier 1 (M2, M3):** the `concatenate` constructor producing a valid
  `StabilizerCode (n₁·n₂) k₂`, all obligations discharged.
- **Tier 1.5 (M4):** `centralizer_classify_of_k1` — the inner centralizer is
  `stabilizer ⊔ ⟨X̄₁, Z̄₁⟩`. **The long pole.** Required by Tier 2.
- **Tier 2 (M5, M6):** block-restriction calculus → induced-outer
  correspondence → distance lower bound + witness → `HasCodeDistance`.
- **Instance (M7):** Steane⊗Steane `= [[49,1,9]]`.

## Milestones (7 PRs, strictly dependency-ordered)

Each PR compiles, is `sorry`-free, and is umbrella-wired (orphan-module trap).

| M | Tier | Goal | LOC | Long pole? |
|---|---|---|---|---|
| M1 | 0 | Embedding calculus: embed inner op into block `b`; weight/support/commutation/multiplicativity | ~260 | |
| M2 | 1a | Promotion map + `ConcatCSSData` + generator list + typing (easy fields) | ~140 | |
| M3 | 1b | Hard `generators_commute` + no-`−I` + independence + logicals → `concatenate` | ~330 | R6 sub-pole |
| M4 | 1.5 | `centralizer_classify_of_k1` (inner centralizer structure) | ~250–350 | **YES (R1)** |
| M5 | 2a | Block restriction + induced-outer correspondence | ~320 | R7 sub-pole |
| M6 | 2b | Distance lower bound + witness → `concat_hasCodeDistance` | ~180 | |
| M7 | — | Steane⊗Steane instance | ~80 | |

**Total: ~1560–1740 LOC across 8 new modules.**

### M1 — Tier 0: embedding/reindexing calculus
- **Files:** `QEC/Stabilizer/Framework/Concatenation/Embedding.lean` (new) +
  umbrella `Framework/Concatenation.lean` (new) → edit `Framework.lean`.
  *(See "Layering" note below — these primitives sit at the Framework layer,
  not Codes, because Promotion (M2) depends on them.)*
- **Key signatures** (`[NeZero n₁]`; zero-phase convention):
  ```lean
  def qIdx (n1 : ℕ) (b : Fin n2) (i : Fin n1) : Fin (n1 * n2)   -- b*n1 + i
  def blockOf (n1 : ℕ) [NeZero n1] (q : Fin (n1 * n2)) : Fin n2 -- q / n1
  def posOf   (n1 : ℕ) [NeZero n1] (q : Fin (n1 * n2)) : Fin n1 -- q % n1
  def embedBlockOp (b) (op : NQubitPauliOperator n1) : NQubitPauliOperator (n1*n2) :=
    fun q => if blockOf q = b then op (posOf q) else PauliOperator.I
  def embedBlock (b) (g : NQubitPauliGroupElement n1) := ofOperator (embedBlockOp b g.operators)
  lemma mulOp_embedBlockOp_operators ...           -- OPERATOR-level (phase-free); NO group embedBlock_mul
  @[simp] lemma embedBlock_phasePower : (embedBlock b g).phasePower = 0 := rfl
  @[simp] lemma weight_embedBlock : (embedBlock b g).weight = g.weight
  lemma weight_eq_sum_block_weights ...
  theorem weight_ge_of_blocks_ge (B : Finset (Fin n2)) (hB : ∀ b ∈ B, d1 ≤ blockWeight b g) : d1 * B.card ≤ g.weight
  theorem embedBlock_commute_iff    : ... ↔ g * h = h * g       -- via commutes_iff_even_anticommutes
  theorem embedBlock_anticommute_iff : ... ↔ Anticommute g h     -- via anticommutes_iff_odd_anticommutes (NO hom route)
  theorem embedBlock_cross_commute (h : b ≠ b') : ...            -- different blocks always commute
  lemma anticommutesAt_count_eq_sum_blocks ...                   -- parity bridge for M3
  ```
- **EXIT:** module builds clean; `weight_embedBlock`, `weight_ge_of_blocks_ge`,
  `embedBlock_{commute,anticommute}_iff`, `embedBlock_cross_commute` `sorry`-free;
  **no group-level `embedBlock_mul` anywhere**; wired into `Framework.lean`.

### M2 — Tier 1a: promotion map + generator list + typing
- **Files:** `Framework/Concatenation/Promotion.lean` (new) → `Framework/Concatenation.lean`.
- **Key signatures:**
  ```lean
  structure ConcatCSSData (n1 n2 k2 : ℕ) [NeZero n1] where
    Cin : StabilizerCode n1 1 ; Cout : StabilizerCode n2 k2
    innerZ innerX : List _ ; inner_split : Cin.generatorsList ~ (innerZ ++ innerX)
    outerZ outerX : List _ ; outer_split : Cout.generatorsList ~ (outerZ ++ outerX)   -- TYPED routing
    innerZ_isZ ... outerX_isX ...                                                     -- CSS typing
    innerLogX_isX : IsXTypeElement (Cin.logicalOps 0).xOp ; innerLogX_phaseZero : ... = 0
    innerLogZ_isZ : IsZTypeElement (Cin.logicalOps 0).zOp ; innerLogZ_phaseZero : ... = 0
  def promoteE (Xbar Zbar) (h : NQubitPauliGroupElement n2) := ofOperator (promoteOp Xbar Zbar h.operators)
  lemma promoteSingle_noY_of_isXType ... ; lemma promoteSingle_noY_of_isZType ...   -- Y↦I branch is dead
  lemma promoteE_isX ... ; lemma promoteE_isZ ...
  def concatGeneratorsList (D) := s1PerBlockList D ++ promotedOuterList D
  lemma concatGeneratorsList_length : ... = n1*n2 - k2
  lemma concatGeneratorsList_phaseZero : AllPhaseZero (concatGeneratorsList D)
  ```
- **EXIT:** module builds clean; `promoteSingle_noY_*`, `promoteE_isX/isZ`,
  `concatGeneratorsList_{length,phaseZero}` `sorry`-free; Y-branch provably dead.

### M3 — Tier 1b: commutation core + constructor
- **Files:** `QEC/Stabilizer/Codes/Concat/Constructor.lean` (new) +
  umbrella `Codes/Concat.lean` (new) → edit `Codes.lean`.
- **Build & verify FIRST, in isolation** (most-reused lemma):
  ```lean
  lemma promote_anticommute_filter_card_parity (D) (h1 h2 : NQubitPauliGroupElement n2) :
      Even (anticommuteCount (promoteE .. h1) (promoteE .. h2)) ↔ Even (anticommuteCount h1 h2)
  ```
- **Then:**
  ```lean
  lemma concat_generators_commute (D) : ...                 -- cases: inner-inner same/cross block; inner-promoted; promoted-promoted
  lemma concat_closure_no_neg_identity (D) : negIdentity (n1*n2) ∉ closure (listToSet (concatGeneratorsList D))
  lemma rowsLinearIndependent_concat (D) : ...              -- via symplectic bridge OR a ConcatCSSData field (fallback)
  def concatLogicalX/Z (D) (ℓ : Fin k2) := promoteE .. (D.Cout.logicalOps ℓ).xOp/.zOp
  lemma concatLogical{X,Z}_mem_centralizer ... ; lemma concatLogical_anticommute ...
  noncomputable def concatenate (D : ConcatCSSData n1 n2 k2) : StabilizerCode (n1 * n2) k2
  ```
- **EXIT:** `concatenate` fully constructed, `sorry`-free; module builds clean;
  `concat_closure_no_neg_identity` via `negIdentity_not_mem_closure_union`
  (`CSSCommutationLemmas.lean:34`) on the regrouped Z∪X generator set.

### M4 — Tier 1.5: inner centralizer classification (the long pole)
- **Files:** `QEC/Stabilizer/Framework/Symplectic/CentralizerStructure.lean`
  (new) → edit `Framework/Symplectic.lean`. *(Lives at the Symplectic layer
  because it depends on `SymplecticSpan.lean`.)*
- **Key signatures:**
  ```lean
  lemma mem_stabilizer_of_operators_eq (C : StabilizerCode n 1) (g) (hg : g ∈ centralizer ..)
      (s) (hs : s ∈ C.toStabilizerGroup.toSubgroup) (heq : s.operators = g.operators) :
      g ∈ C.toStabilizerGroup.toSubgroup        -- via mul_inv_operators_identity_of_eq_operators (phase/Y-agnostic)
  theorem mem_stabilizer_of_commutes_both_logicals (C : StabilizerCode n 1) (g)
      (hg : g ∈ centralizer ..) (hX : commutes g X̄1) (hZ : commutes g Z̄1) :
      g ∈ C.toStabilizerGroup.toSubgroup        -- the decisive direction the weak dichotomy lacked
  theorem centralizer_classify_of_k1 (C : StabilizerCode n 1) (g) (hg : g ∈ centralizer ..) :
      g ∈ C.toStabilizerGroup.toSubgroup ∨ IsNontrivialLogicalOperator g C.toStabilizerGroup
  ```
- **Strategy:** the operator-part of any centralizer element lies in the
  symplectic dual of the stabilizer rows (`mem_closure_implies_symp_in_span` +
  commutation = symplectic-orthogonality). For k=1, `dim(dual/stab) = 2`,
  spanned by X̄/Z̄. `exists_mem_closure_of_symp_in_span` realizes any in-span
  operator as a closure element; `mem_stabilizer_of_operators_eq` upgrades
  operator-equality to group-equality.
- **EXIT:** the three lemmas `sorry`-free; module builds clean; **whole-repo
  `lake build` clean** (new global content — global-content discipline).
  **Develop in parallel with M2/M3** (touches only `Framework/Symplectic`).

### M5 — Tier 2a: block restriction + correspondence
- **Files:** `QEC/Stabilizer/Codes/Concat/Restriction.lean`,
  `QEC/Stabilizer/Codes/Concat/Correspondence.lean` (new) → `Codes/Concat.lean`.
- **Key signatures:**
  ```lean
  def restrictBlock (b) (g : NQubitPauliGroupElement (n1*n2)) : NQubitPauliGroupElement n1 :=
    ⟨0, fun i => g.operators (qIdx b i)⟩
  lemma weight_eq_sum_restrictBlock (g) : g.weight = ∑ b, (restrictBlock b g).weight
  lemma restrictBlock_mem_centralizer (D) (g) (hg : g ∈ centralizer (concatenate D)) (b) :
      restrictBlock b g ∈ centralizer D.Cin.toStabilizerGroup
  def inducedOuter (D) (g) : NQubitPauliGroupElement n2          -- one 2-bit class per block (k1=1)
  lemma inducedOuter_support_eq : b ∈ (inducedOuter D g).support ↔ IsNontrivialLogicalOperator (restrictBlock b g) Cin   -- USES M4
  theorem inducedOuter_mem_centralizer (D) (g) (hg) : inducedOuter D g ∈ centralizer D.Cout.toStabilizerGroup
  theorem inducedOuter_not_mem_stabilizer (D) (g) (hg : IsNontrivialLogicalOperator g (concatenate D)) :
      inducedOuter D g ∉ D.Cout.toStabilizerGroup.toSubgroup    -- coset injectivity, USES M4
  theorem inducedOuter_isNontrivialLogical (D) (g) (hg) :
      IsNontrivialLogicalOperator (inducedOuter D g) D.Cout.toStabilizerGroup  -- 3rd clause via zOp/xOp_operators_ne_of_mem
  ```
- **EXIT:** `inducedOuter_isNontrivialLogical` `sorry`-free using M4 (not the
  weak dichotomy); modules build clean.

### M6 — Tier 2b: distance lower bound + witness + main theorem
- **Files:** `QEC/Stabilizer/Codes/Concat/Distance.lean` (new) → `Codes/Concat.lean`.
- **Key signatures:**
  ```lean
  theorem weight_ge_d1_mul_d2 (D) (h1 : HasCodeDistance Cin d1) (h2 : HasCodeDistance Cout d2)
      (g) (hg : IsNontrivialLogicalOperator g (concatenate D)) (hw : 0 < g.weight) : d1 * d2 ≤ g.weight
  noncomputable def concatWitness (D) (h1) (h2) : NQubitPauliGroupElement (n1*n2)   -- X-type, phase 0
  lemma concatWitness_weight : (concatWitness D h1 h2).weight = d1 * d2
  lemma concatWitness_isNontrivialLogical : IsNontrivialLogicalOperator (concatWitness ..) (concatenate D)
  theorem concat_hasCodeDistance (D) (h1) (h2) : HasCodeDistance (concatenate D) (d1 * d2)
    -- hasCodeDistance_of: ≥1 (Nat.mul_pos) + witness + min (contrapositive of weight_ge_d1_mul_d2)
  ```
- **EXIT:** `concat_hasCodeDistance` `sorry`-free; module builds clean. **Headline result.**

### M7 — concrete instance: Steane⊗Steane
- **Files:** `QEC/Stabilizer/Codes/Concat/SteaneSteane.lean` (new) → `Codes/Concat.lean`.
- **Key signatures:**
  ```lean
  def steaneConcatData : ConcatCSSData 7 7 1 := { Cin := steaneCode, Cout := steaneCode, ... }
  noncomputable def steaneConcat : StabilizerCode 49 1 := concatenate steaneConcatData
  theorem steaneConcat_distance : HasCodeDistance steaneConcat 9 :=
    concat_hasCodeDistance steaneConcatData steane_d3 steane_d3
  ```
- **EXIT:** `steaneConcat_distance` `sorry`-free; whole-repo `lake build` clean;
  `native_decide` for the n=49 check-matrix field if `rowsLinearIndependent_concat`
  is the fallback.

## File-by-file map and layering

| Module | Path | Layer | Umbrella edit |
|---|---|---|---|
| Embedding (Tier 0) | `Framework/Concatenation/Embedding.lean` | Framework | new `Framework/Concatenation.lean` → `Framework.lean` |
| Promotion (Tier 1a) | `Framework/Concatenation/Promotion.lean` | Framework | `Framework/Concatenation.lean` |
| Centralizer (Tier 1.5) | `Framework/Symplectic/CentralizerStructure.lean` | Framework.Symplectic | `Framework/Symplectic.lean` → `Framework.lean` |
| Constructor (Tier 1b) | `Codes/Concat/Constructor.lean` | Codes | new `Codes/Concat.lean` → `Codes.lean` |
| Restriction (Tier 2a) | `Codes/Concat/Restriction.lean` | Codes | `Codes/Concat.lean` |
| Correspondence (Tier 2a) | `Codes/Concat/Correspondence.lean` | Codes | `Codes/Concat.lean` |
| Distance (Tier 2b) | `Codes/Concat/Distance.lean` | Codes | `Codes/Concat.lean` |
| Steane instance (M7) | `Codes/Concat/SteaneSteane.lean` | Codes | `Codes/Concat.lean` |

**Layering subtlety (important):** the embedding/promotion primitives are pure
index + operator algebra over `Foundations` only — they have **no Codes
dependency**, so they belong in `Framework/Concatenation/`, *not* `Codes/Concat/`.
Only the constructor/restriction/distance/instance (which use `StabilizerCode`)
live under `Codes/Concat/`. This respects
`Foundations < {Geometry, Framework.Core} < Framework.{Symplectic, Homological} < Codes`.

**Orphan-module trap:** every new `.lean` MUST be appended to its immediate
umbrella, which chains to `Stabilizer.lean`. Create `Framework/Concatenation.lean`
(imports Embedding + Promotion) and add it to `Framework.lean`; create
`Codes/Concat.lean` (imports the four Codes/Concat modules) and add it to
`Codes.lean`; add `CentralizerStructure` to `Framework/Symplectic.lean`.

**Noncomputable discipline:** `concatenate`, `steaneConcat`, `concatWitness`
(anything through `Subgroup.closure` / the `NQubitPauliGroupElement` group
instance) are `noncomputable def`. `qIdx`/`blockOf`/`posOf`/`embedBlockOp`/
`promoteOp` are plain computable `def`; `embedBlock`/`promoteE` are plain `def`
(just `ofOperator ∘ …`) unless the elaborator demands otherwise.
`[NeZero n₁]` is a `variable`, never a global instance. M4 adds a global
*lemma* (not instance) — still run whole-repo `lake build`.

## Lemma dependency graph

```
Foundations (exist): ofOperator{_phasePower,_operators}, commutes_iff_even_anticommutes,
  anticommutes_iff_odd_anticommutes, anticommutesAt, weight/support, mul_inv_operators_identity_of_eq_operators
Framework.Symplectic (exist): mem_closure_implies_symp_in_span, not_mem_subgroup_of_symp_not_in_span,
  exists_mem_closure_of_symp_in_span, negIdentity_not_mem_of_indep_phase_zero_commute, SymplecticOrthogonal
Framework.Core.Logical (exist): IsNontrivialLogicalOperator_iff, xOp/zOp_operators_ne_of_mem, commutes_of_operators_identity
Framework.Core.CSS (exist): negIdentity_not_mem_closure_union, IsZ/XTypeElement{,_of_mem_closure}

M1 Embedding:  qIdx → blockOf/posOf → embedBlockOp → embedBlock
   sum_over_block_eq → mulOp_embedBlockOp_operators (operator-level)
   support/weight → weight_eq_sum_block_weights → weight_ge_of_blocks_ge
   parity atoms → embedBlock_{commute,anticommute}_iff, embedBlock_cross_commute, anticommutesAt_count_eq_sum_blocks
M2 Promotion:  ConcatCSSData ; promoteE ; promoteSingle_noY_* → promoteE_isX/isZ
   concatGeneratorsList → _length, _phaseZero ; concat_listToSet_eq_union
M4 Centralizer (parallel): mem_stabilizer_of_operators_eq → mem_stabilizer_of_commutes_both_logicals → centralizer_classify_of_k1
M3 Constructor: promote_anticommute_filter_card_parity → concat_generators_commute → concat_closure_no_neg_identity
   concatLogical{X,Z}_mem_centralizer, concatLogical_anticommute ; rowsLinearIndependent_concat → concatenate
M5 Restriction/Correspondence: restrictBlock → weight_eq_sum_restrictBlock ; restrictBlock_mem_centralizer
   inducedOuter ; inducedOuter_support_eq (←M4) ; inducedOuter_mem_centralizer
   inducedOuter_not_mem_stabilizer (←M4) → inducedOuter_isNontrivialLogical
M6 Distance: weight_inducedOuter_ge_d2 → card_nontrivialBlocks_ge_d2 ; weight_ge_d1_mul_d2
   concatWitness → _weight, _isNontrivialLogical → concat_hasCodeDistance
M7 Instance: steaneConcatData → steaneConcat → steaneConcat_distance
```

## Risk register

| ID | Source | Sev | Item | Mitigation | M |
|---|---|---|---|---|---|
| R1 | distance #4/#5/#6 | BLOCKING | Lower bound needs "commutes-with-both-logicals ⟹ stabilizer"; weak dichotomy insufficient | Author M4 on the *existing* `SymplecticSpan` bridge, not from scratch. Do NOT advertise a cheap route. | M4 |
| R2 | constructor #2 | BLOCKING | Two contradictory `embedBlock` phase conventions; group-level `embedBlock_mul` truth depends on convention | Zero-phase `ofOperator` everywhere; operator-level `mulOp_embedBlockOp_operators`; delete group-level `embedBlock_mul`. | M1 |
| R3 | constructor #3 | BLOCKING | Promoting raw `Cout.generatorsList` through lossy `Y↦I` is unsound | Promote over typed `outerZ ++ outerX`; `promoteSingle_noY_*` makes Y-branch dead. | M2 |
| R4 | distance #1, #4 | SERIOUS | `restrictBlock b g` can be Y-class (X̄₁Z̄₁); CSS-typing it is unsound | Use phase/Y-agnostic `mul_inv_operators_identity_of_eq_operators` + `commutes_of_operators_identity` (exist). | M4, M5 |
| R5 | constructor #4 | SERIOUS | `generators_independent` promoted/inner separation = `symp(X̄₁) ∉ span(inner rows)` | Use `not_mem_subgroup_of_symp_not_in_span` (exists). Fallback: `rowsLinearIndependent_concat` as a `ConcatCSSData` field, `native_decide` per instance. | M3 (fallback M7) |
| R6 | distance #7, constructor #1 | SERIOUS | Promoted-gen "commute on the nose" parity; per-block odd-parity dependency | `promote_anticommute_filter_card_parity` — build & verify FIRST, standalone. Atom = `(Cin.logicalOps 0).anticommute`. | M3 |
| R7 | distance #5 | SERIOUS | `inducedOuter_not_mem_stabilizer` = coset injectivity; shares M4's theorem | Gated on M4; budget ~90 LOC. Block-by-block reduction via `centralizer_classify_of_k1`. | M5 |
| R8 | constructor #1 | MINOR | `embedBlock_anticommute_iff` via homomorphism route is unsound | Prove via parity only; homomorphism route deleted. | M1 |
| R9 | distance #11 | MINOR | Parity bridge must never *multiply* two promoted elements | Keep correspondence parity-based (`Finset.card`), never `promoteE_mul`. | M5 |
| R10 | distance #12 | MINOR | 3rd `IsNontrivialLogicalOperator` clause for induced/witness | Use existing `xOp/zOp_operators_ne_of_mem` (phase-agnostic). | M5, M6 |
| R11 | distance #2/#3 | MINOR | `restrictBlock_mem_centralizer` needs `embedBlock` closure transport | Operator-level lemma (M1) + `Subgroup.closure_induction`. | M5 |

**Long pole: R1 / M4.** Single mandatory framework theorem; gates all of Tier 2.
Schedule it in parallel with M2/M3. If M4 slips, M1–M3 still land and give a
usable `concatenate` constructor (no distance theorem). **Do NOT attempt M5/M6
before M4 is `sorry`-free** — they are unsound without it (no weak-dichotomy
shortcut exists). De-risk M4 first by spiking `mem_stabilizer_of_commutes_both_logicals`
for fixed Steane (n=7, where `native_decide` sanity-checks the dimension-2 claim).

## Verification strategy

- **MCP-first loop:** `lean_diagnostic_messages` (severity error) → `lean_goal`
  → `lean_multi_attempt` (3+ candidates) → Edit → re-diagnose → one `lake build`
  at PR-commit time only. Never run `lake build` concurrently with the MCP LSP.
  `lean_local_search` before guessing names.
- **`decide`/`native_decide` CAN:** `qIdx` bounds, `Fin 4` phase arithmetic,
  and the **n=49 check-matrix independence** via `rowsLinearIndependent_iff_forall`
  (a finite F₂ check — feasible; M7/R5 fallback). Use **`decide` not
  `native_decide`** for any `Anticommute` goal (kernel reduces, native does not).
- **The 4ⁿ wall:** the distance lower bound at n=49 is NOT brute-forceable —
  minimizing weight over nontrivial logicals ranges over ~`4⁴⁹ ≈ 3×10²⁹` Paulis.
  M5/M6 must be genuine structural proofs; there is no decide-shortcut.
- **Per-milestone gate:** M4 and M7 additionally require a whole-repo `lake build`
  (new global content). Final acceptance: `lean_verify` on
  `concat_hasCodeDistance` and `steaneConcat_distance` to confirm axiom hygiene.

## Recommended ordering

1. **M1 first** (no deps; unblocks everything). Land `sum_over_block_eq` before the parity lemmas.
2. **M4 in parallel with M2/M3** (independent layer). Spike the n=7 Steane case first.
3. **M2 → M3.** Build `promote_anticommute_filter_card_parity` standalone before cases A/B/C. If R5 overruns, demote `rowsLinearIndependent_concat` to a `ConcatCSSData` field.
4. **M5 → M6** (both gated on M4). Budget M5's `inducedOuter_not_mem_stabilizer` generously.
5. **M7 last** (mechanical; `native_decide` for the n=49 field).

**Natural cut-point:** M1–M3 alone deliver a verified `concatenate` constructor
with no distance claim — independently valuable. M4–M6 (the distance theorem)
are the deeper, higher-risk deliverable and can be a follow-on.

## Estimated effort

| Tier | M | LOC | Notes |
|---|---|---|---|
| 0 | M1 Embedding | ~260 | pure index/operator algebra |
| 1a | M2 Promotion + typing | ~140 | |
| 1b | M3 Constructor | ~330 | commute ~150, indep ~90, logicals ~70, packaging ~20 |
| 1.5 | M4 Centralizer | ~250–350 | **long pole**; highest uncertainty |
| 2a | M5 Restriction + Correspondence | ~320 | R7 sub-pole |
| 2b | M6 Distance + witness | ~180 | |
| — | M7 Steane⊗Steane | ~80 | |

Total **~1560–1740 LOC**. Realistic schedule risk concentrated in M4.
</content>

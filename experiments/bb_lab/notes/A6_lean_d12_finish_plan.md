# A6 — Finishing the Lean `d = 12` proof: formalization plan

**Produced by** the `bb-d12-formalization-plan` workflow (2026-06-13): 7 parallel
understanding agents → 2 per-Prop strategists → (adversarial stress-tests +
synthesis, cut short by an API rate-limit storm; the two cruxes below were then
verified directly and this synthesis written by hand from the recovered Phase-1/2
output). Workflow run: `wf_65fdeda3-b3b` (34 agents, ~2.3M tokens).

---

## 0. Bottom line

`HasCodeDistance grossStabilizerCode 12` is currently **conditional** on two
assumed Props — `LightStabilizerClassification` (DangerousSector.lean:528) and
`MImBound` (SafeSector.lean:179). Discharging both makes d = 12 **unconditional**.
The analytic mathematics is already complete and adversarially reviewed
(A4_writeup.md + A3 confined-floor program); the remaining work is purely
*formalization*.

- **Neither Prop is brute-forceable.** Both quantify over `f : BaseGroup → ZMod 2`
  (BaseGroup = `ZMod 6 × ZMod 6`, 36 elts ⇒ 2³⁶ ≈ 7×10¹⁰ functions). Even after
  quotienting to `im ∂₂` (F₂-dim 30, ≈10⁹) a head-on `native_decide` is infeasible.
- **Both reduce to feasible finite checks — but only behind an analytic spine.**
  The shared backbone is the **CRT layer frame** `F₂[Z₆²] ≅ F₂[Z₂²] × (F₄[Z₂²])⁴`
  (A4 §3). Build it once; both Props consume it.
- **The single genuine research risk is that frame.** Verified: mathlib's
  `GaloisField 2 2 = SplittingField (X⁴-X)` is *noncomputable*, and
  `ZMod.chineseRemainder` only covers `ZMod (m·n)` — there is **no mathlib analogue**
  for the group-algebra DFT / the `(ZMod 2)[X]/(X⁶-1) ≅ F₂×F₂×F₄` decomposition, and
  every off-the-shelf field/CRT object is noncomputable (fatal to `native_decide`).
  A bespoke **computable F₄ (`Fin 4` + tables)** and a hand-proved frame isomorphism +
  component-vanishing lemmas are prerequisites.
- **Effort.** `LightStabilizerClassification`: hard-but-doable, ≈ 3–5 PR-sized
  milestones. `MImBound`: research-grade frame + ≈ 4–6 milestones of finite leaves.
  Realistically multi-week, frame-gated.
- **Honest fallback.** If the frame proves intractable, the current state
  (d ≥ 6 unconditional, d = 12 conditional on the two Props) is already a clean,
  publishable result. `MImBound` is the natural thing to leave assumed last.

---

## 1. The two Props, side by side

| | `LightStabilizerClassification` | `MImBound` |
|---|---|---|
| **File** | DangerousSector.lean:528 | SafeSector.lean:179 |
| **Statement** | every nonzero base 2-boundary `b = ∂₂f` of weight ≤ 11 is a **hexagon** `∂₂δ_g` or a **D-pair** `∂₂(δ_g + δ_{g+d})`, `d ∈ pairDirections` | every chain `seamC ζ + ∂₂f` (ζ ∈ ker ∂₂, not itself a base boundary) has `chainWeight ≥ 12` |
| **Consumer** | `dangerous_sector_of_classification` — demands a **constructive witness** `g`/`g+d` (feeds `dangerous_hexagon_bound`/`dangerous_dpair_bound`), not just a weight bound | `safe_sector_of_mim` (uses deck homotopy R) |
| **Quantifier** | ∀ `b ∈ im ∂₂` (dim 30 ≈ 10⁹) | outer ∀ζ ∈ ker ∂₂ (64 elts) × inner ∀f mod im ∂₂ |
| **Finite residue** | **252** light boundaries (36 hexagons wt 6 + 216 D-pairs wt 10; no wt 8); per-shape `native_decide` leaves ≈ 10⁵ over weight-≤5 lighter-block supports of `Fin 36` | 63 nonzero ζ → **5 translation orbits**; §11 16-cell/33-bucket, §12 ~48 cells (~4096/side), §13 **118** ρ-link kills, **512** M-table configs — all in validated `native_decide` range |
| **Irreducibly analytic core** | **Parity** (\|b\| even) + **Floor** (both blocks ≥3 nonzero `Z₂²` layers) + **sharp one-block** `\|B·z'\| ≥ 16` | §9.4 component-vanishing (off₀=off₂=0, c₁=c₂=0); §10 slot-cost / chord-slope / achiever-structure spine |

**Convention bridge** (do not skip): repo `∂₂f = (A⋆f \| B⋆f)` has the A-block at
`j=0`, B-block at `j=1` (BBChainComplex.lean:208); A4 writes `∂₂z = (B·z, A·z)`.
**Repo-left = lab-right.** Every "lighter block" / left-right reference in A4 §§6,9–14
flips when transcribing.

---

## 2. Verified cruxes (the stress-test conclusions)

- **Crux 1 — mathlib has no usable frame (CONFIRMED by grep).**
  `GaloisField 2 2` is noncomputable; `ZMod.chineseRemainder` is `ZMod`-only; no
  group-algebra DFT exists. ⇒ build a computable `F₄ := Fin 4` with explicit add/mul
  tables, prove the field/`DecidableEq`/`Fintype` API, and assemble the frame
  isomorphism + component transforms by hand. This is the load-bearing infra and the
  main risk.
- **Crux 2 — native_decide scale.** MImBound's leaves are all ≤ ~4096 (validated:
  DangerousSector.lean:159-347 runs `native_decide` at 36–432-element BaseGroup scale,
  Phase-5 decoder probe ran 5184 cases in ~5 s). **LightStab's per-shape ~10⁵ Fin-36
  enumeration is the one unvalidated number** (3 orders above current). Plausibly fine
  **iff** coded as *plain weight-bounded tuples* — NOT `conv`-based predicates
  (~10⁶ ⇒ OOM exit 137) and NOT `Finset.powersetCard` (minutes + GBs per lemma). Must
  be probed before committing (see M0).
- **Crux 3 — boundary-membership decidability.** `b ∈ im ∂₂` is a
  `LinearMap.range` existential, undecidable as stated; the frame makes it the
  **decidable parity check** `H_A · (A-block of b) = 0` with `H_A = nullspace(A_mapᵀ)`
  (cf. `a3_shape_lemmas.py` `in_imA`/`in_imB`). Probe this early too.
- **Crux 4 — Phase-5 lesson applies.** Concrete noncomputable defeq + `native_decide`
  is a kernel-whnf hazard. Keep F₄ and the transforms **computable and explicit**, and
  reuse the **abstract-helper / chain-abstract** pattern that fixed Phase 5 §6.

---

## 3. Critical path: the shared CRT-frame infrastructure (build first)

New module, e.g. `QEC/Stabilizer/Codes/BivariateBicycle/CRTFrame.lean`:

1. **`F4` computable** — `Fin 4` (or an inductive) + add/mul tables; instances
   `CommRing`/`Field`, `DecidableEq`, `Fintype`. Verify field axioms by `decide`.
2. **Component transforms `V_j`** — the four maps `(BaseGroup → ZMod 2) → (Z₂² → F4)`
   as explicit `Finset` sums over characters ψ_j (A4 §3 lines 110-175). Plus the
   trivial component `V₀ : … → F₂[Z₂²]`.
3. **Multiplicativity** `V_j(P ⋆ z) = P̂_j · ẑ_j` — the *single load-bearing identity*
   (today only machine-checked on 200 random z). Either prove analytically or
   `native_decide` it over the finite component spaces (16 each) for `P ∈ {A,B}`.
4. **Engine support-shape lemma** — a nonzero radical-ideal element is *constant* or
   *co-point*, hence has **≥3 nonzero layers** (A4 §6.2 lines 347-359). Frame-dependent;
   feeds both Floor and the sharp one-block bound.

---

## 4. Recommended route per Prop

- **`LightStabilizerClassification` → Route R-C (hybrid).** Keep analytic only:
  Parity (reuse `cycle_weight_even`, BaseDistance.lean:175) + **Floor** + **sharp
  one-block ≥16** (both via the frame fragment §3.3–3.4). Then the six-shape resolution
  + block→b endgame + **constructive witness** become a translation-normalized finite
  enumeration over weight-≤5 lighter-block supports of `Fin 36`, gated by the decidable
  `in_imA` parity check, discharged by `native_decide` with the explicit **252-boundary
  table** as the witness oracle. (R-A full-analytic = research-grade overkill; R-B
  CRT-free = blocked, Floor has no CRT-free proof.)
- **`MImBound` → Route R2 (CRT-reduce-then-native_decide), sequenced behind an R3
  warm-up.** R3 first: parity + `base_cycle_weight_ge_6` give ≥6 on the coset using
  ONLY existing infra — this surfaces the boundary-membership-decidability blocker and
  validates the `ζ → ker ∂₂ → 5-orbit` reduction *before* committing to the frame.
  Then R2: frame + §9.4 vanishing + §10 spine ⇒ the §11/§12/§13/M-table `native_decide`
  leaves. Feasibility honestly "low" — the frame is the wall, the leaves are easy.

---

## 5. Staged milestones (dependency-ordered)

| # | Milestone | Kind | Diff | Acceptance |
|---|---|---|---|---|
| **M0** | De-risking probe file (scratch, à la `phase5/Probe.lean`) | native_decide | low | (a) a 10⁵-scale plain-tuple weight-≤5 `Fin 36` enumeration compiles in budget; (b) `in_imA`-style membership `native_decide`s; (c) computable `F4` field axioms + one `V_j` multiplicativity instance over all components `native_decide` green |
| **M1** | `F4` computable + instances | infra | low-med | `Field F4`, `DecidableEq`, `Fintype`, tables verified |
| **M2** | Component transforms `V_j` + multiplicativity | infra | med | `V_j(A⋆z)=Â_j ẑ_j`, `V_j(B⋆z)=B̂_j ẑ_j` proven (or `native_decide`d over components) |
| **M3** | Engine support-shape / radical dichotomy | analytic | high | nonzero radical elt ⇒ ≥3 nonzero layers |
| **M4** | Floor (both blocks ≥3 layers) + sharp one-block ≥16 | analytic | high | the two lower bounds over `im ∂₂` |
| **M5** | 252-boundary classification + constructive witness ⇒ **discharge `LightStabilizerClassification`** | native_decide | med | `dangerous_sector_of_classification` no longer takes `hC` |
| **M6** | `ker ∂₂` = 5-orbit reduction + §9.4 vanishing (off₀=off₂=0, c₁=c₂=0) | infra/analytic | high | 63 ζ → 5 reps; component-vanishing proven |
| **M7** | §10 slot frame: slot-cost rules, chord-slope, achiever-structure | analytic | research | the confined-floor spine |
| **M8** | §11/§12/§13 leaves + 512 M-table | native_decide | med | S(a,b) buckets, per-cell floors, 118 ρ-link kills all `native_decide` |
| **M9** | Assemble ⇒ **discharge `MImBound`** ⇒ unconditional `gross_pauli_distance_eq_12` ⇒ drop `hC`,`hMim` from `grossStabilizerCode_hasCodeDistance_12` | assembly | med | axiom audit: no extra hypotheses |

M0–M5 close LightStab; M6–M9 close MImBound. M1–M2 are shared infra on the critical
path of both.

---

## 6. Risk register

| Risk | Severity | Killer scenario | Mitigation |
|---|---|---|---|
| **R1 CRT frame** (M2/M3/M6/M7) | critical / research | the multiplicativity or §9.4 vanishing identity is itself a ∀-over-2³⁶ that resists both analytic Lean and `native_decide` | the component identities live over *finite* component spaces (16 each) ⇒ `native_decide` per component; only the cross-z universal needs the analytic frame |
| **R2 LightStab 10⁵ leaf** (M5) | high | `native_decide` OOM/timeout at 10⁵ Fin-36 tuples | M0 probe; plain tuples (no `conv`/`powersetCard`); shard per shape; `maxRecDepth 4096` |
| **R3 membership decidability** (M0) | medium | `b ∈ im ∂₂` not expressible as a decidable check | build `H_A`/`H_B` parity matrices; prove `b ∈ im ∂₂ ↔ H·b = 0` |
| **R4 noncomputable whnf** | medium | frame defs + `native_decide` reignite the Phase-5 kernel-whnf runaway | keep F4/transforms computable + explicit; abstract-helper pattern; trust `lake build` over LSP |

---

## 7. The concrete first move

Write `experiments/bb_lab/phase6/Probe.lean` (mirror the Phase-5 decoder de-risking):

1. **Scale probe** — `native_decide` a 10⁵-scale enumeration: `∀` weight-≤5 supports of
   `Fin 36` (as plain `List`/tuple, not `Finset.powersetCard`), check a cheap predicate.
   Confirms M5 fits the kernel budget. *This single check decides whether R-C is viable.*
2. **Membership probe** — define `H_A` from the boundary matrix; `native_decide`
   `b ∈ im ∂₂ ↔ H_A·b = 0` on a handful of `b`. De-risks Crux 3 / R3.
3. **Frame probe** — define computable `F4 := Fin 4` + tables; `decide` the field axioms;
   `native_decide` one `V_j` multiplicativity instance over all 16×16 component inputs.
   De-risks the M1/M2 core.

If all three are green, R-C (LightStab) and R2 (MImBound) are de-risked and M1 begins.
If the scale probe (1) fails, fall back to per-shape sharded leaves or push more of the
classification into the analytic Floor argument.

---

## 8. M0 probe — EXECUTED, GREEN (2026-06-13)

`experiments/bb_lab/phase6/Probe.lean`, run via `lake env lean` in **40 s** (exit 0,
no errors):

- **Probe A (computable F₄).** A `Fin 4` + explicit add/mul-table model satisfies all
  field axioms by `decide` (commutative add with char 2, commutative mul with unit,
  distributivity, nonzero inverses). ⇒ the bespoke computable F₄ for the CRT frame
  (M1) is confirmed viable — no dependence on mathlib's noncomputable `GaloisField`.
- **Probe B (∂₂ sparse-syndrome scale).** The boundary-2 sparse syndrome
  (`term2At`/`synd2`, the ∂₂ analog of `BaseDistance.syndAt`) `native_decide`s the
  36³ ≈ 4.7·10⁴ three-face sweep cleanly and fast.

**Scale conclusion (Crux 2 resolved):** the repo's *committed*
`BaseDistance.smallCycleCheck_four` already `native_decide`s the ∂₁ sparse form at
`(BaseGroup × Fin 2)³ ≈ 3.7·10⁵` plain tuples. Probe B confirms the ∂₂ form behaves
the same. The two together **bracket** the real `LightStabilizerClassification` leaf
(C(36,≤5) ≈ 4.4·10⁵): correct boundary form ✓, 10⁵-scale ✓. So the R-C finite leaf is
NOT a `native_decide`-budget gamble — the validated scale is ~10⁵, not the ~400 I
initially feared. (Caveat: keep the real leaf as plain weight-bounded tuples + a light
per-case count; the over-scoped 1.68·10⁶ sweep with `Finset.filter.card` per case did
NOT finish in ~14 min and was dropped — that allocation-per-case pattern, not the case
count, was the cost.)

**Net effect on the plan:** the M1/M2 infra (computable F₄ + transforms) and the
LightStab finite leaf (M5) are de-risked. The residual genuine research risk is
unchanged and localized to the **analytic frame identities** — multiplicativity
`V_j(P⋆z)=P̂_j ẑ_j` (M2), the radical support-shape lemma (M3/M4), and the §9.4/§10
confined-floor spine for MImBound (M6/M7).

---

## 9. Workflow cross-check + further verified probes (2026-06-13)

A second, independent multi-agent run (`bb-d12-formalization-plan`, 19 agents) produced
a more detailed plan — see **`A7_d12_finish_plan.md`** (20-milestone critical path + a
stress-tested risk register). It **agrees** on architecture and **sharpens** two things:

1. **Two more `phase6/` probes, written + run by the workflow agents, re-verified by hand:**
   - `EngineProbe.lean` — **GREEN (10.2s)**: `Ann(D)=(D)`, `D²=0`, and the ≥3-layer
     dichotomy over the 256-element `F₄[Z₂²]` ring are a genuine finite `native_decide`.
     **This downgrades the radical support-shape lemma (M3/M4 above) from "analytic
     research risk" to a finite kernel check** — a real correction to §0/§8's framing.
   - `FrameProbe.lean` — **GREEN (2.6s)**: multiplicativity `V₁(A·δ_p)=Â₁·V₁(δ_p)` on the
     36-chain basis. Multiplicativity (M2) is likewise demonstrated finite, not research.
   - `LeafProbe.lean` — GREEN but its scale sub-probe is **vacuous** (`synd2…=synd2…`
     tautology); discount its 1.68×10⁶ claim. Real scale bracket = `smallCycleCheck_four`
     (3.7×10⁵). [[bb-gross-formalization-phases]] memory records this.

2. **The genuine research risk relocates to `M-COLLAPSE`** — the *join lemma* tying the
   green finite `F₄`-table leaves to the actual **noncomputable** `bb72Complex.chainWeight
   (seamC ζ + ∂₂f)`. Killer scenario (3 stress lenses, "hard-but-doable", low conf):
   leaves green in isolation but never bridged to the real definition, **or the
   noncomputable `chainWeight` reignites the Phase-5 kernel-whnf blowup**. Mitigation:
   sequence behind LightStab, state the join lemma *about `chainWeight`* first (via the
   computable `bb72Complex_chainWeight_eq` bridge, `CoverTransfer.lean:228`), and reuse
   the Phase-5 abstract-helper discipline. Plus a new infra risk: the **`V_j`
   F₂-linearity bridge** (F₄-as-`Fin 4` has no `Module` instance ⇒ hand-rolled) — the one
   delicate `CRTFrame.lean` piece (~600–800 lines total).

**Updated bottom line:** everything *computational* (F₄, the engine ring-facts,
multiplicativity, the LightStab leaf) is now demonstrated tractable. The sole remaining
gamble is the **leaf-to-`chainWeight` join for MImBound**, and it is cost/surprise risk,
not impossibility. Recommended first move (per A7 §7): a `MembershipProbe.lean`
(decidable `b ∈ im ∂₂ ↔ H·b=0` + a *real* gated six-shape leaf) and bank the `M-R3`
≥6-coset warm-up — then promote the green probes into `CRTFrame.lean` and drive LightStab
to drop `hC` before attempting `M-COLLAPSE`.

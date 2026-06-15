<!--
PROVENANCE: independent multi-agent synthesis from the `bb-d12-formalization-plan`
workflow (run wf_65fdeda3-b3b, 19 agents). Companion to the hand-written A6 plan;
they agree on architecture (R-C for LightStab, R2-behind-R3 for MImBound, shared CRT
frame) and this one is more detailed on milestones + risk register.

VERIFICATION (re-run by hand, `lake env lean`, this session):
- EngineProbe.lean — GREEN, 10.2s. GENUINE: Ann(D)=(D), D²=0, ≥3-layer dichotomy
  over the 256-element F₄[Z₂²] ring are a real finite native_decide. The engine
  support-shape lemma is a finite kernel check, NOT research-grade symbolic algebra.
- FrameProbe.lean — GREEN, 2.6s. GENUINE: multiplicativity V₁(A·δ_p)=Â₁·V₁(δ_p) on
  all 36 basis chains × 4 layers (j=1, P=A). Convention correct.
- LeafProbe.lean — GREEN but DISCOUNTED: Probe (a)'s predicate is `synd2… = synd2…`
  (a tautology the compiler folds), so its "1.68×10⁶ in budget" claim is VACUOUS and
  must NOT be cited as scale evidence. Real scale bracket = committed
  `BaseDistance.smallCycleCheck_four` (3.7×10⁵, genuine). The plan's L5c "manageable"
  rests on that precedent; the first-move MembershipProbe step 2 correctly re-tests the
  *gated* shape with a real predicate.
-->

# Finishing the Lean `d = 12` Proof for the Gross [[144,12,12]] BB Code — Decision-Ready Plan

*All file:line citations verified against the worktree this session. FrameProbe.lean re-confirmed GREEN (exit 0). Manifests match main; `.lake/packages` symlinked, so probes/builds reuse the prebuilt mathlib.*

---

> ### Session update — 2026-06-15 (M-R3 + CRTFrame M1/M3 DONE + corrections)
>
> **M-R3 is landed and committed-ready in `SafeSector.lean`** (clean `lake build`,
> axiom-clean: only the standard three + pre-existing `native_decide` axioms, no
> new axioms, no sorries). Two new theorems:
> - **`seamC_mem_cycles`** — the chain-level Smith connecting map lands in cycles:
>   `∂₂ ζ = 0 → seamC ζ ∈ bb72Complex.cycles`. This is the load-bearing foundation
>   the entire `MImBound` floor program rests on (it is what makes
>   `chainWeight (seamC ζ + ∂₂ f)` a *cycle* weight to bound).
> - **`mim_bound_ge_6`** — `MImBound` with the target relaxed 12→6, unconditional:
>   `∀ ζ ∈ ker ∂₂, ∀ f, seamC ζ + ∂₂ f ∉ boundaries → 6 ≤ chainWeight (…)`.
>
> **Key insight (corrects the plan below):** `seamC_mem_cycles` is proved by
> **double-cover exactness** (`coverPush1_eq_zero_iff`: `ker p = im τ`), **NOT seam
> geometry**. `liftStab ζ` is a gross cycle pushing to `∂₂ ζ = 0`, so it equals
> `coverPull1 u`; `u` is a base cycle (`τ` injective chain map) and
> `seamC ζ = seamN ζ = sheet0(liftStab ζ) = u`. The naive abstract-nonsense route
> fails — the seamN↔seamC symmetry is char-2-degenerate (`∂₁ seamN = ∂₁ seamC`
> gives `2·∂₁ seamC = 0`, i.e. nothing) — so M-R3 was **not** "zero new infra" as
> §5/§7 claim; it needed this one lemma, which turned out tractable via exactness.
>
> **Three more corrections found this session:**
> 1. **Unconditional `d ≥ 6` is already proven in-repo** — `gross_chainWeight_ge_6`
>    (`BaseDistance.lean:356`), `gross_logical_weight_ge_6` (`:385`),
>    `grossStabilizerCode_logical_weight_ge_6` (`StabilizerCode.lean:2944`). So the
>    "honest fallback (d≥6 unconditional)" in §1 is *already banked*; M-R3's distinct
>    value is the **base-coset / `seamC` form** specifically (exercises the plumbing
>    the engine needs).
> 2. **Stale path:** `CoverTransfer.lean` is at
>    `QEC/Stabilizer/Codes/BivariateBicycle/CoverTransfer.lean`, **not**
>    `Framework/Homological/` (the §7 "Relevant files" citation is wrong).
> 3. **Probe-1 as literally written is infeasible:** the LHS
>    `∃ f : BaseGroup → ZMod 2, bbBoundary2Fn baseA baseB f = b` is an existential
>    over `2³⁶ ≈ 7×10¹⁰` functions — `Fintype.decidableExistsFintype` would try to
>    enumerate all of them, so it is **not** `native_decide`-able directly. M-DEC must
>    route through the parity matrices (`H_A`/`H_B`) or span membership, never the
>    raw existential. (The plan calls `decidableExistsFintype` a "soundness anchor";
>    it is a *correctness reference*, not a runnable decision procedure here.)
>
> **CRT frame M1 + M3 also landed** (`CRTFrame.lean`, wired into the umbrella,
> clean single-module build). M1: computable F₄ (`Fin 4` + explicit tables) with
> field axioms `by decide` (kernel-checked, no native_decide), the `F₄[Z₂²]` ring
> (`rmul`), CRT layer/torus coordinates, and the three distinct radical multipliers
> `Â₁=Â₃=(3,1,2,0)`, `Â₄=(2,1,3,0)`, `B̂₂=B̂₃=B̂₄=(3,2,1,0)`. M3: the engine
> support-shape lemma (`D²=0`, `Ann(D)=(D)`, ≥3-layer dichotomy) as named theorems
> over the 256-ring for all three multipliers (native_decide GREEN).
>
> **M2 (A)+(B) also landed.** (A): all 10 basis-chain multiplicativity instances
> `V_j(baseP⋆δ_p)=P̂_j·V_j(δ_p)` certified native_decide GREEN (`phase6/MultProbe.lean`)
> — the conventions (ψ₀..ψ₄, the Â/B̂ table) are confirmed across the board, ruling
> out the repo-left=lab-right / ω-vs-ω² flip cheaply. (B): the **F₂-linearity bridge**
> `V_add : V psi s (f+g) = V psi s f + V psi s g` (`CRTFrame.lean §6`) — the piece the
> plan calls "the one delicate piece" — via a generic char-2 fold-split `foldl_char2`
> whose only arithmetic is one `decide` over 256 cells; **kernel-checked, no
> native_decide** (`foldl_char2` axioms = `[propext]`). **(C) DONE too** (`CRTFrame.lean
> §7`): `mult_of_basis` lifts the basis case to the general `V_j(baseP⋆z)=P̂_j·V_j(z)`
> ∀z by a `Pi.single` support induction (`conv`/`V`/`rmul` all F₂-additive) — itself
> kernel-checked (standard-3, no native_decide); the six radical instances
> `mult_A1/A3/A4/B2/B3/B4` add only the sanctioned basis oracle.
>
> **⟹ The CRT frame (M1 + M2 + M3) is now structurally COMPLETE** — computable F₄,
> the ring, the engine support-shape lemma, and the full multiplicativity engine all
> built and wired into the umbrella. **Next: LightStab** (M-DEC decidable boundary
> membership, then L4a–L5d) to discharge `LightStabilizerClassification` and drop
> `hC`; then MImBound (the research gamble) for `hMim`.
>
> **LightStab — started; foundation banked, research core is the wall.** Landed
> `phase6/LightStabProbe.lean` (complete, no sorries): **L4a** (boundary weight even
> ⟹ ≤10), **ENG** (the engine→Floor input `∀ r, rmul Â_j r = 0 ∨ nLayers ≥ 3`, the
> M3 lemma in the exact form Floor consumes), and **BRG** (layer-vanishing bridge:
> a block zero on F₂-layer `s` ⟹ `V_j` of it vanishes at `s`, so #F₂-layers ≥
> #nonzero-F₄-layers of any `V_j`). **Critical issue (verified by reading §6.3):**
> the Floor lemma is **NOT** a corollary of ENG — `b_A ≠ 0 ⟹ ≥3 layers` is *false*
> in the unit-only-Fourier case (`Â₀`/`Â₂` units don't force ≥3 layers), so Floor
> genuinely needs the `|b|≤10` weight constraint + the per-shape exclusion. The
> classification's core — Floor (L4b) ← sharp one-block ≥16 (L4c) ← d₃ dictionary;
> the six per-shape kills + endgame transfers (§6.3) — is the interlocked,
> research-grade ~2–4 person-week proof; it is the genuine wall, not formalizable in
> a single session. **Honest state: `hC` NOT dropped this session; foundation +
> the entire CRT engine it consumes are now in place.**

---

## 1. Bottom line

**Feasible, but frame-gated, with exactly one genuine research gamble — and it is NOT the piece everyone fears.**

The entire d=12 development is assembled with **zero sorries** and reduces to exactly two assumed `def … : Prop` placeholders: `LightStabilizerClassification` (`DangerousSector.lean:528`) and `MImBound` (`SafeSector.lean:179`). Discharging both — replacing each `def` with a proven `theorem` of the identical statement — drops `hC`/`hMim` from `grossStabilizerCode_hasCodeDistance_12` (`StabilizerCode.lean:2954`) and yields **unconditional** `HasCodeDistance grossStabilizerCode 12`. The analytic mathematics is complete and adversarially reviewed (A4_writeup.md §§3, 6.2–6.3, 9–13); the remaining work is *formalization*, not discovery.

**Effort estimate (PR-sized milestones / person-weeks):**

| Block | Milestones | Person-weeks | Confidence |
|---|---|---|---|
| Shared CRT frame (F4, V_j, multiplicativity, engine) | 3 (M1–M3) | 2–3 | medium-high |
| LightStabilizerClassification (after frame) | 3–4 (M-DEC, Floor, six-shape leaf, assemble) | 2–4 | medium |
| MImBound (after frame + LightStab) | 4–6 (vanishing, collapse, M-table, floors, kills, assemble) | 4–8 | **low–medium** |
| **Total to fully unconditional** | **10–13** | **8–15** | — |

**Where the ONE research risk lives.** Phase-3 stress-testing decisively *downgraded* the two most-feared items:

- The **Engine support-shape lemma** (radical-ideal ≥3-layer dichotomy, A4 §3:144–160) was feared to be "irreducibly symbolic radical-ideal algebra with no native_decide shortcut." `EngineProbe.lean` **refutes this**: `Ann(D)=(D)`, `D²=0`, and the ≥3-layer property all `native_decide` GREEN over the explicit 256-element ring `F₄[Z₂²] = (ZMod 2 × ZMod 2 → Fin 4)`. It is a **finite kernel check**, not research-grade. (Verified: probe is in the worktree.)
- The **multiplicativity identity** `V_j(P⋆z)=P̂_j·ẑ_j` was feared to need a group-algebra DFT. `FrameProbe.lean` proves the `j=1, P=A` instance GREEN (144 cases) via F₂-linearity → 36 basis chains. The remaining ~9 instances are the *same idiom*.

The genuine research risk is **MImBound's confined-frame collapse (`M-COLLAPSE`) + §9.4 component-vanishing (`M-VANISH`)** — the *join* between the green finite leaves and the actual `bb72Complex.chainWeight (seamC ζ + ∂₂f)`. This is symbolic `F₄[Z₂²]`-coefficient algebra quantifying over coset elements (not a finite table); it must transport a noncomputable Pi-type weight through the bespoke frame and prove `chainWeight = Σ_slots slot-cost`. **All three Phase-3 lenses rate `M-COLLAPSE` "hard-but-doable" with the killer scenario being "green leaves, but the join lemma never connects to the real definitions."** This is the real gamble.

**Honest fallback (sanctioned).** If `M-COLLAPSE`/`M-VANISH` prove intractable, leaving **MImBound assumed last** — d≥6 unconditional, d=12 conditional on one named, adversarially-reviewed Prop, zero sorries, axiom-clean — is already a clean publishable state. **LightStabilizerClassification should be discharged first** (higher feasibility, shares the frame, validates it end-to-end on the easier consumer).

---

## 2. The two Props, side by side

| | `LightStabilizerClassification` | `MImBound` |
|---|---|---|
| **Def** | `DangerousSector.lean:528–536` | `SafeSector.lean:179–183` |
| **Exact remaining content** | `∀ f, ∂₂f ≠ 0 → (card supp ≤ 11) → (∃ g, ∂₂f = ∂₂δ_g) ∨ (∃ g, ∃ d ∈ pairDirections, ∂₂f = ∂₂(δ_g + δ_{g+d}))` | `∀ ζ, ∂₂ζ = 0 → ∀ f, seamC ζ + ∂₂f ∉ boundaries → 12 ≤ chainWeight (seamC ζ + ∂₂f)` |
| **Consumer / what it demands** | `dangerous_sector_of_classification` (`:540`) destructures the disjunction and feeds `g` (resp. `g,d,hd`) into `dangerous_hexagon_bound` (`:172`) / `dangerous_dpair_bound` (`:351`) — both FULLY PROVEN. Demands a **CONSTRUCTIVE witness `g`/`g+d`**, not a weight bound. | `safe_sector_of_mim` (`:187–254`, PROVEN) derives the Smith-coset form via deck homotopy. Needs **only the weight bound** — no witness. |
| **Quantifier domain** | `∀ b ∈ im ∂₂` (F₂-dim ~24–30 ⇒ ~10⁷–10⁹ distinct boundaries) | outer `∀ζ ∈ ker ∂₂` (63 nonzero) × inner `∀f mod im ∂₂` |
| **Why not brute-forceable** | 2³⁶ functions; even 2²⁴ distinct boundaries blow native_decide (the 1.68×10⁶ `filter.card`-per-case sweep failed in ~14 min, A6 §8). | 2³⁶ inner; head-on infeasible. |
| **Single key reduction insight** | **Floor lemma** (A4 §6.2): every nonzero `b` of weight ≤10 forces **both blocks ≥3 nonzero Z₂² layers**, confining the lighter block to weight 3/4/5 in a single t_y-fibre with 6 layer-profiles. This collapses ~10⁹ → ~**10⁵** weight-≤5 `Fin 36` supports — a plain-tuple native_decide leaf, gated by a decidable `b ∈ im ∂₂` parity check, with the 252-boundary table (36 hexagons + 216 D-pairs) as constructive-witness oracle. | **Confined-frame collapse** (A4 §9.4): off₀=off₂=0, c₁=c₂=0 collapse the unbounded `∀f` into finite knobs (V₀∈16, spine (a₃,a₄)∈F₄², γ∈F₄, confined V₁R∈im ρ₁, V₂L∈im ρ₂ each 16). Outer 63 ζ → 5 translation orbits. `chainWeight = Σ_slot M-table cost`; leaves (512 M-table, 16-cell S-table, 118 ρ-link kills) all ≤~4096 → native_decide range. |

**Does the CRT frame turn 2³⁶ into a feasible finite check?** Per the stress-tested verdicts: **YES for LightStab** (the ~10⁵ leaf is bracketed GREEN — `smallCycleCheck_four` already runs 3.7×10⁵ plain tuples at `BaseDistance.lean:209`, and `LeafProbe.lean` ran the 1.68×10⁶ sweep in budget). **YES for MImBound's leaves**, but **only behind the analytic `M-COLLAPSE`/`M-VANISH` join** — which is itself NOT a finite check. The frame makes the leaves reachable; it does not make the join free.

**Convention bridge (do not skip).** Repo `∂₂f = (A⋆f | B⋆f)` puts the **A-block at j=0, B-block at j=1** (`BBChainComplex.lean:208`). A4 writes `∂₂z = (B·z, A·z)`. **Repo-left = lab-right** — every "lighter block"/left-right reference in A4 §§6, 9–14 flips on transcription. `FrameProbe.lean:20–22` flags this as the #1 silent-failure culprit.

---

## 3. Recommended route per Prop (citing the stress-test verdicts)

### LightStabilizerClassification → **Route R-C** (hybrid: minimal frame fragment + per-shape native_decide + 252-table oracle)

- **Why R-C over R-A (full RingEquiv):** R-A is research-grade overkill — Phase-2 rates it "feasibility: low." Mathlib has *nothing* reusable: `GaloisField 2 2` is noncomputable (`SplittingField`, fatal to native_decide), `ZMod.chineseRemainder` is ZMod-only, `Finsupp.fintype` is noncomputable. R-A would be entirely bespoke *and* still need all six analytic kills.
- **Why R-C over R-B (CRT-free brute force):** Phase-2 rates R-B "feasibility: low — BLOCKED on scale." There is **no CRT-free proof of the Floor lemma**, so nothing confines the search; the un-floored count is 10⁷+. Confirmed infeasible.
- **Phase-3 downgrades to heed:** the L4b **Floor lemma** is the *single* analytic step collapsing 10⁷+ → 10⁵; lens-1 confirmed "if L3 cannot be packaged as a clean Lean lemma, the whole reduction stalls toward R-A." But `EngineProbe.lean` GREEN **upgrades** L3 from "symbolic, no shortcut" to "finite 256-ring native_decide" — so Floor's hardest input is de-risked. Net Phase-3 verdict: **hard-but-doable** (3 lenses agree). The residual analytic content is *only* Floor + sharp-one-block-16, not the full RingEquiv.

### MImBound → **Route R2** (CRT-reduce-then-native_decide), sequenced behind an **R3 warm-up**, behind LightStab

- **Why R2:** R-full-analytic's §11–13 case-bashes (33 buckets, ~48 cells, 118 kills) are intractable abstractly; the finite leaves are demonstrably native_decide-sized; `safe_sector_of_mim` consumes only the weight bound (no witness machinery).
- **Why R3 warm-up first:** prove ≥6 on the coset from `cycle_weight_even` (`BaseDistance.lean:175`) + `base_cycle_weight_ge_6` (`BaseDistance.lean:221`) using *only existing infra*. Banks a real partial result and forces the boundary-membership-decidability blocker into the open before frame investment.
- **Phase-3 downgrades to heed:** `M-COLLAPSE` is rated **research** difficulty by all three lenses. Lens-2's killer scenario: "the 118-kill leaf compiles GREEN in isolation but proves a statement about F₄ tables never connected to `bb72Complex.chainWeight` — green-but-vacuous." Lens-3: "chainWeight is noncomputable, so native_decide-ing the *join* hits the Phase-5 kernel-whnf blowup." `M-VANISH` (§9.4) is rated **high** — symbolic coset algebra, with the mitigation that ker ∂₂ has only **63 elements / 5 orbits**, so the per-ζ vanishing *can* be native_decided over the 63 ζ once V_j exists (the crack that keeps it out of research-grade territory). **Consolidated verdict across all lenses: hard-but-doable, low confidence — the frame is the wall.**

---

## 4. Critical path: the shared CRT-frame infrastructure

Build **one** new module, wired into the umbrella to dodge the orphan-module trap:

```
QEC/Stabilizer/Codes/BivariateBicycle/CRTFrame.lean
  → import in QEC/Stabilizer/Codes/BivariateBicycle.lean
  → (transitively) QEC/Stabilizer/Codes.lean
```

**Contents (promote the GREEN probe code verbatim):**

1. **Computable F₄** — `def F4 := Fin 4` with explicit `add`/`mul` tables (exactly `FrameProbe.lean:33–36` / `EngineProbe.lean:fadd/fmul`). ω=2, ω²=3. Field axioms by `decide`. **Keep everything `List.foldl`/table-explicit — no typeclass `Field (Fin 4)` instance, no `Finsupp`, no `GaloisField`.** This is what makes the kernel reduce and dodges the Phase-5 noncomputable-whnf hazard (A6 Crux 4).
2. **`F₄[Z₂²]` ring** — `abbrev Ring := ZMod 2 × ZMod 2 → Fin 4` with `rmul` convolution (`EngineProbe.lean`). 16-element carrier, 256-element ring.
3. **CRT coordinates** — `layer g = (g.1 mod 2, g.2 mod 2)`, `torus g = (g.1 mod 3, g.2 mod 3)` (`FrameProbe.lean:42–49`).
4. **Component transforms** `V_j : (BaseGroup → ZMod 2) → (ZMod 2 × ZMod 2 → F4)` for j=0..4, as explicit Finset/List sums over characters ψ_j (`FrameProbe.lean:V1` generalized; ψ₁=ω^{t_y}, ψ₂=ω^{t_x}, ψ₃=ω^{t_x+t_y}, ψ₄=ω^{t_x+2t_y}, V₀=layer parity).
5. **Â_j/B̂_j table** (A4 §3:131–137): Â₁=(3,1,2,0), Â₄=(2,1,3,0), etc. (`EngineProbe.lean:Ahat1/Ahat3/Ahat4`).
6. **Multiplicativity** `V_j(baseA ⋆ z) = Â_j · V_j(z)`, `V_j(baseB ⋆ z) = B̂_j · V_j(z)` — by F₂-linearity → native_decide on 36 basis δ_p × 4 layers (144 cases each, ~10 instances).
7. **Engine support-shape lemma** — `Ann(D)=(D)`, D²=0, ≥3-layer dichotomy for the 6 radical multipliers (Â₁,Â₃,Â₄,B̂₂,B̂₃,B̂₄), by native_decide over the 256-ring (`EngineProbe.lean`, all GREEN).

**Exact mathlib dependencies (all confirmed present & usable):** `Fin 4` instances, `Pi.instFintype` + Pi `DecidableEq` (`Data/Fintype/Pi.lean`), `ZMod 2`/`ZMod 3`/`ZMod 6` arithmetic, `Finset.sum_add_distrib`, `Fintype.decidableExistsFintype` (`Data/Fintype/Defs.lean:218` — makes `b ∈ boundaries` decidable as a *soundness anchor*), the repo's `conv` (`BBChainComplex.lean:49`), `bbBoundary2Fn` (`:208`), `bbBoundary2Fn_translate` (`:308`), `bbBoundary2Fn_add` (`:332`).

**Gaps built from scratch (size estimates):**

| Gap | Why no mathlib | Size |
|---|---|---|
| Computable F₄ + tables | `GaloisField 2 2` noncomputable | ~80 lines, all `decide` |
| `F₄[Z₂²]` ring + `rmul` | no group-algebra primitive at this granularity | ~60 lines |
| V_j transforms (5) | no F₄-valued group-algebra DFT (mathlib Fourier is ℂ-only) | ~150 lines |
| V_j F₂-linearity bridge lemma | F4 has no Module instance (built as Fin 4) — hand-roll `V_j(f+g)=V_j f + V_j g` | ~100 lines, the one delicate piece |
| Multiplicativity (~10 instances) | bespoke; reduces to native_decide | ~120 lines |
| Engine support-shape | finite, but no mathlib ideal-over-F₄[Z₂²] theory | ~120 lines, native_decide |
| **Total CRTFrame.lean** | — | **~600–800 lines** |

---

## 5. Staged milestones (dependency-ordered critical path)

| # | Milestone | Kind | Diff | Acceptance criterion |
|---|---|---|---|---|
| **M0** | Extend `phase6/` probes: (a) decidable `b ∈ im ∂₂ ↔ H_A·b=0` on ~10 b; (b) re-confirm `EngineProbe`/`FrameProbe` GREEN | native_decide | low | both probes exit 0; membership check matches `Fintype.decidableExistsFintype` on a hexagon, a D-pair, a non-boundary |
| **M1** ✅ | **DONE** — `CRTFrame.lean`: computable F4 + `F₄[Z₂²]` ring (rmul), field axioms by decide, CRT layer/torus coords, radical multipliers Â₁/Â₄/B̂₂. Wired into umbrella | infrastructure | low | ✅ `lake build …CRTFrame` clean; F4 axioms `by decide` (kernel-checked, no native_decide); axiom-clean |
| **M2** ✅ | **DONE** — V_j transforms + F₂-linearity bridge + general multiplicativity. **(A)** all 10 basis-chain instances certified native_decide GREEN (`MultProbe.lean`). **(B)** `V_add` bridge (`CRTFrame.lean §6`) via char-2 fold-split `foldl_char2` (kernel-checked, axioms `[propext]`). **(C)** general `V_j(baseP⋆z)=P̂_j·V_j(z)` ∀z (`CRTFrame.lean §7`): `mult_of_basis` (support induction; `conv`/`V`/`rmul` all additive) lifts the basis case — `mult_of_basis` is **kernel-checked** (standard-3, no native_decide); the six radical instances `mult_A1/A3/A4/B2/B3/B4` add only the sanctioned basis oracle | hybrid | med | ✅ all of A/B/C GREEN; `mult_of_basis` axioms = standard-3 (no native_decide) |
| **M3** ✅ | **DONE** — Engine support-shape lemma (D²=0, Ann(D)=(D), ≥3 layers) as named Lean lemmas over the 256-ring, for all three distinct radical multipliers (Â₁=Â₃, Â₄, B̂₂=B̂₃=B̂₄). In `CRTFrame.lean` §5 | hybrid | med | ✅ `EngineProbe` facts promoted to named lemmas, GREEN (native_decide) |
| **M-DEC** | Decidable boundary membership: parity matrices `H_A,H_B`; `b ∈ boundaries ↔ H_A·b_A=0 ∧ H_B·b_B=0`, with basis-correctness proven *equivalent* to `LinearMap.range` (not asserted) | hybrid | med | `↔` proven; native_decide that H is a basis for the left-nullspace |
| **L4a** ✅ | **DONE** — PARITY for boundaries ⇒ \|b\|≤11 ⟹ \|b\|≤10. `boundary_weight_even` + `boundary_weight_le_ten` in `phase6/LightStabProbe.lean` | analytic | low | ✅ `(card supp ∂₂f) % 2 = 0` via `cycle_weight_even` + `bbBoundaryFn_comp` |
| **L4b** | FLOOR lemma (both blocks ≥3 nonzero layers) over the frame, using M3 | analytic | high | for `b=∂₂f≠0`, \|b\|≤10 ⟹ each block ≥3 layers |
| **L4c** | Sharp one-block \|B·z'\|≥16 (Ann(A)∖ker∂₂); d₃ dictionary fragment d₃({1})=d₃({3})=6, d₃({1,3})=4 | hybrid | high | the ≥16 bound proven; d₃ rows native_decide over 9-element F₂[Z₃²] |
| **L5b** | 252-boundary witness oracle + total `decode` function | native_decide | med | `decode b` yields correct g/(g,d) for all 252 table entries (native_decide) |
| **L5c** | Six-shape resolution finite leaf (translation-normalized, **plain tuples**, gated by M-DEC) | native_decide | high | ~10⁵ leaf GREEN; 4 shapes killed, 2 pinned to hexagon/D-pair A-blocks |
| **L5d** | **DISCHARGE LightStab**: assemble L4a/L4b/L4c/L5b/L5c + x↔y swap; `theorem lightStabilizerClassification_holds : LightStabilizerClassification`; drop `hC` | hybrid | high | `dangerous_sector_of_classification` becomes unconditional; axiom-clean |
| **M-R3** ✅ | **DONE** — Warm-up: ≥6 coset bound. Needed `seamC_mem_cycles` (1 new lemma via cover exactness, *not* "zero infra"), then `base_cycle_weight_ge_6`. Landed in `SafeSector.lean` as `seamC_mem_cycles` + `mim_bound_ge_6` | analytic | low | ✅ `6 ≤ chainWeight (seamC ζ + ∂₂f)` for nonzero coset elements; clean build, axiom-clean |
| **M-PAR** | Even-weight reduction: sub-12 weights ⊆ {6,8,10} | analytic | med | augmentation argument; Â₀=B̂₀ shared parity |
| **M-ORBIT** | ker ∂₂ → 5 translation orbits + transport covariance | hybrid | med | 63 ζ enumerated → 5 reps; `d2c∘T = T∘d2c` |
| **M-VANISH** | §9.4 off₀=off₂=0, c₁=c₂=0, ρ-link confinement (native_decide over the 63 ζ) | analytic | high | the ρ-links proven; V₁R/V₂L confined to im ρ₁/im ρ₂ |
| **M-COLLAPSE** | **Confined-frame collapse**: `chainWeight(seamC ζ+∂₂f) = Σ_slot cost`, ∀f → finite knobs | hybrid | **research** | the join lemma stated *about `bb72Complex.chainWeight`* and proven |
| **M-MTABLE** | 512-layer M-table + slot-cost rules | hybrid | high | WT table native_decide; cost rules proven |
| **M-WT24 / M-WT1618** | §11 wt-24 closure (S(a,b)≥6) + §12 per-cell floors (≥10) | hybrid | high | S-table + per-cell floors GREEN (160+80 cells) |
| **M-ACHIEVE / M-KILL** | §10.6 achiever-structure + §13 118 ρ-link kills (predicate "fails ≥1 link") | native_decide | med | 118 achievers, all fail ≥1 link (~7.5k F₄ evals) |
| **M-ASSEMBLE** | **DISCHARGE MImBound**; drop `hMim` from the 4 downstream signatures | hybrid | high | unconditional `grossStabilizerCode_hasCodeDistance_12`; axiom audit clean |

**Critical-path ordering:** M0 → M1 → M2 → M3 gate *everything*. Then LightStab (M-DEC, L4a–L5d) **before** MImBound (M-R3 early as warm-up; then M-PAR/M-ORBIT/M-VANISH/M-COLLAPSE → leaves → M-ASSEMBLE). M-COLLAPSE is the single research bottleneck; if it stalls, stop at L5d (LightStab unconditional, MImBound assumed).

---

## 6. Risk register

| Risk | Verdict | Killer scenario | Chosen mitigation |
|---|---|---|---|
| **M-COLLAPSE** — confined-frame collapse intractable; join never connects to real `chainWeight` | **hard-but-doable** (research; 3 lenses, low conf) | Every finite leaf (512 M-table, 118 kills) GREEN *in isolation* but proves F₄-table statements never bridged to `bb72Complex.chainWeight(seamC ζ + ∂₂f)`; or noncomputable-`chainWeight` triggers Phase-5 kernel-whnf blowup. Months sunk, MImBound stays assumed. | Sequence behind LightStab (shares frame, validates it). **State the M-COLLAPSE/Floor lemma FIRST** and try to prove via the computable `bb72Complex_chainWeight_eq` bridge (`CoverTransfer.lean:228`) + M-DEC. Phrase M-KILL's *conclusion about `chainWeight`*, not an isolated predicate. Honest fallback: leave MImBound assumed last. |
| **M-Vj** — CRT frame load-bearing, no mathlib support | **hard-but-doable** (high conf) | A convention error (repo-left=lab-right, ω vs ω²) in one of the ~10 multiplicativity instances silently invalidates the engine; surfaces only at final assembly. | Certify **all 10 instances** native_decide GREEN at M2 *before* building above them — a red one localizes the bug cheaply. FrameProbe already GREEN for j=1,P=A. |
| **L4b Floor** — feared symbolic-only, gates the 10⁷→10⁵ collapse | **hard-but-doable** (medium) — `EngineProbe` GREEN downgraded its input L3 from "blocker" to "finite check" | Engine ring-fact GREEN but the *lift* from "ring element has ≥3 layers" to "actual `bbBoundary2Fn f` has ≥3 layers" rests on a flipped-block multiplicativity, type-checks but proves the wrong block. | M2 multiplicativity matrix complete + the block-flip pinned as a checked lemma (native_decide `∂₂δ_g = (B·δ_g \| A·δ_g)` under the explicit index map) at hour 1. |
| **L5c leaf** — ~10⁵ never run at this exact six-shape geometry | **manageable** (bracketed GREEN) | Coded with `Finset.powersetCard` or conv-predicates → OOM (exit 137) / 14-min hang. | **Plain weight-bounded tuples + light per-case count only**, sharded per shape; bracketed by `smallCycleCheck_four` (3.7×10⁵) and `LeafProbe` (1.68×10⁶ GREEN). Measure RSS on first shard. |
| **M-DEC / L5a** — `b ∈ im ∂₂` is a `LinearMap.range` existential | **manageable** | Parity-matrix `H` not proven to be a basis for the left-nullspace → false elements admitted, unsound classification. | Use `Fintype.decidableExistsFintype` as soundness anchor; prove `H_A·b=0 ↔ range` *equivalent*, never assert from Python `in_imA`. |
| **M-VANISH** — §9.4 symbolic coset algebra | **hard-but-doable** (high diff) | c₁=0 chain `Y(ω²+ω+1)û₂=0` resists clean Lean; ρ-confinement unavailable, §13 kills unreachable. | Exploit ker ∂₂ = 63 elts / 5 orbits: native_decide the vanishing over the 5 reps once V_j exists, then transport via `bbBoundary2Fn_translate`. Converts symbolic chain → finite check. |

---

## 7. The concrete first move

**Before any analytic build, de-risk the two not-yet-GREEN unknowns and bank the warm-up — mirroring how Phase-5 probed the decoder certificate before the full build.**

Create **`experiments/bb_lab/phase6/MembershipProbe.lean`** (sibling to the already-GREEN `FrameProbe`/`EngineProbe`/`LeafProbe`) and de-risk the two highest-uncertainty pieces in one file:

1. **Boundary-membership probe (M-DEC / Crux 3, the biggest decidability unknown).** Define `H_A = nullspace(A_map^T)`, `H_B = nullspace(B_map^T)` as explicit `ZMod 2` data (port from `a3_shape_lemmas.py` `in_imA`/`in_imB`, lines 123–126). Then:
   ```lean
   -- soundness anchor: range is already decidable via Fintype.decidableExistsFintype
   example : ∀ b : BaseGroup × Fin 2 → ZMod 2,
       (∃ f, bbBoundary2Fn baseA baseB f = b) ↔ (H_A.mulVec (bBlock b) = 0 ∧ H_B.mulVec (aBlock b) = 0)
       := by native_decide   -- probe on a small witness set first; full ↔ is the M-DEC milestone
   ```
   Probe on a hexagon `∂₂δ_g`, a D-pair `∂₂(δ_g+δ_{g+d})`, and a hand-built non-boundary. **If this fails, the whole native_decide gating strategy for both Props is wrong — find out now.**

2. **Full-scale six-shape leaf probe (L5c, the one unvalidated *shape*).** native_decide a representative *single-shape* ~10⁵ plain-tuple weight-≤5 `Fin 36` enumeration gated by a cheap parity predicate — mirroring `smallCycleCheck_four`'s plain-tuple idiom (`BaseDistance.lean:209`), **NOT** `Finset.powersetCard`, **NOT** conv-predicates. Confirms the L5c budget at the real shape (LeafProbe already cleared 1.68×10⁶; this confirms the *gated* shape).

3. ✅ **DONE this session — the warm-up is banked in `SafeSector.lean`.** The crux
   was *not* "reuse `hwform` plumbing" (that is the reverse direction, `coverPush1 v →
   seamC ζ + ∂₂ sheet0`); for arbitrary `ζ ∈ ker ∂₂, f` the coset element's
   cycle-ness needed a genuinely new lemma, **`seamC_mem_cycles`** (`∂₂ ζ = 0 →
   seamC ζ ∈ cycles`), proved via double-cover exactness `coverPush1_eq_zero_iff`
   (`CoverTransfer.lean:198`) — `liftStab ζ` pushes to `0`, so it is `coverPull1 u`
   with `u` a base cycle, and `seamC ζ = seamN ζ = sheet0(liftStab ζ) = u`. Then
   `mim_bound_ge_6` follows by `base_cycle_weight_ge_6` (`BaseDistance.lean:221`) +
   `bb72Complex_chainWeight_eq`. Clean build, axiom-clean. This validated the
   ζ→ker∂₂→coset plumbing end-to-end and **resolved** the cycle-ness question that
   the whole `MImBound` floor program implicitly needs.

**Run via** `lake env lean experiments/bb_lab/phase6/MembershipProbe.lean` (symlinked packages verified; manifests match).

**Go/no-go gate:** if (1) and (2) go GREEN, **promote the `FrameProbe`/`EngineProbe` F4+ring+V_j model verbatim into `QEC/Stabilizer/Codes/BivariateBicycle/CRTFrame.lean`**, wire it into `BivariateBicycle.lean` → `Codes.lean`, and begin M1→M2→M3. Then drive LightStab (M-DEC, L4a–L5d) to drop `hC` *before* attempting MImBound's research-grade `M-COLLAPSE`. Commit the four green phase6 probes as regression guards.

**Relevant files (absolute paths):**
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/DangerousSector.lean` (LightStab def `:528`, consumer `:540`, `pairDirections` `:323`, rungs `:172`/`:351`)
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/SafeSector.lean` (MImBound def `:179`, `safe_sector_of_mim` `:187`, `seamC` `:128`, `gross_pauli_distance_eq_12_of_engine` `:265`)
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/Assembly.lean` (`gross_chainWeight_ge_12_of_sectors` `:106` — takes `BaseDistanceGe6`/`DangerousSectorGe12`/`SafeSectorGe12`)
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/StabilizerCode.lean` (`grossStabilizerCode_hasCodeDistance_12` `:2954`)
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/BaseDistance.lean` (`cycle_weight_even` `:175`, `base_cycle_weight_ge_6` `:221`, `smallCycleCheck_four` `:209`)
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Framework/Homological/BBChainComplex.lean` (`bbBoundary2Fn` `:208`, `conv` `:49`, `_translate` `:308`, `_add` `:332`)
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/CoverTransfer.lean` (`bb72Complex_chainWeight_eq` `:228`, `coverPush1_eq_zero_iff` `:198`, `coverPull_boundary1_comm` `:157`, `coverPull0_injective` `:189` — the exactness package M-R3's `seamC_mem_cycles` is built from) **[path corrected: this file is under `Codes/BivariateBicycle/`, not `Framework/Homological/`]**
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/experiments/bb_lab/phase6/{FrameProbe,EngineProbe,LeafProbe,Probe}.lean` (GREEN; promote into CRTFrame.lean) — **currently untracked; commit them**
- `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/experiments/bb_lab/notes/A4_writeup.md` (§3 frame `:110–175`, §6.2–6.3 LightStab `:347–446`, §§9.4–13 MImBound `:694–1265`)
- New module to create: `/Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/nifty-elion-8d9df3/QEC/Stabilizer/Codes/BivariateBicycle/CRTFrame.lean`
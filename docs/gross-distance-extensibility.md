# Anatomy and extensibility of the d(gross)=12 proof

Companion to [`gross-distance-proof.md`](gross-distance-proof.md). It maps the
distinct parts of that proof and records, for each, how tightly the argument is
welded to the specific code versus how far it transfers to other bivariate-bicycle
(BB) codes. It also records the **doubling template** the proof instantiates, two
corrections to an earlier (coarser) pass at this analysis, and an independently
**verified second instance** of the template outside the gross lineage.

Scope note: the structural / proof-theoretic content here is grounded in the proof
text and (for the new pair) in a 32/32-check computation. A handful of *quantitative
corpus* claims (the 16,867-code cover sweep; the `Z₆×Z₁₄` weight-8 count; the
two-gross self-test) come from the `bb_lab` cover-cascade tooling and the analysis
agents and are flagged inline as **[reported, not re-verified here]**.

---

## 1. The logical spine (A → B → C → D)

Both codes are read as a length-3 chain complex over `F₂[G]` (`∂₁ = H_X`,
`∂₂ = H_Zᵀ`, `Z`-distance = min weight over nonzero `H₁` classes). The gross group
`Z₁₂×Z₆` is the **free Z₂ double cover** of the base `Z₆×Z₆` in the x-direction.

- **Theorem A** — base floor: no nonzero base `Z`-cycle has weight ≤ 5, so
  `d(base)=6` and `μ_Z(base)=6`, with explicit weight-6 witness `z*`.
- **Theorem B** — cheap cover floor: the sheet-sum projection `p` has `|v|≥|p(v)|`,
  giving `d(gross) ≥ min{d(base), μ_Z(base)} = 6`.
- **Theorem C** — sharp dangerous sector (`[p(v)]=0`): a slice identity reduces it
  to the base-stabilizer inequality `|b| + 2·m(b) ≥ 12`, closed by classifying every
  light base stabilizer (hexagons + D-pairs) and bounding off-support minima.
- **Theorem D** — assembly: dangerous logicals clear 12 by C; *safe* logicals
  (`[p(v)]≠0`) are confined to a nonzero Smith class by homotopy theorem (R) and
  cleared by the slot-frame floor (Prop 32); `d_X=d_Z` by duality; the weight-12
  diagonal lift `τ(z*)` proves tightness.

The factor-of-two `12 = 2·d(base)` is the **cover's gift**; every *number* fed into
it comes from the polynomial-specific base analysis.

---

## 2. Distinct parts, tiered by code-specificity

Four tiers, from most to least portable:

- **generic_BB** — works for any BB code over a finite abelian group.
- **cover_class** — works for any BB code admitting the relevant free Z₂ cover;
  monomial- and group-agnostic.
- **group_CRT_class** — relies on the group factorization (here `Z₆ = Z₂×Z₃`).
- **polynomial_specific** — relies on the exact monomials of `A, B`.

| Mechanism | Tier | Reaches / reuse |
|---|---|---|
| Chain substrate + augmentation parity (PAR) | **generic_BB** | every BB code; PAR's strong form `ε(A)=ε(B)=1` needs odd-weight `A,B` (here both 3). High reuse. |
| X–Z inversion duality (Lemma 1) | **generic_BB** | every BB code, any abelian `G`; already parametric in Lean. High reuse. |
| Free Z₂ cover scaffolding (sheets, σ, block `∂`, `p`, `τ`, dichotomy) | **cover_class** | any free Z₂ cover. High reuse. |
| Theorem B floor `d(gross) ≥ min{d, μ_Z}` | **cover_class** | thin wrapper; imports its number from A. High reuse. |
| Slice identity reducing C to `\|b\|+2m(b)≥12` | **cover_class** | any deck-symmetric block boundary. High reuse. |
| Theorem D assembly shell | **cover_class** | delivers only ≥ d(base) alone; the value is carried by A/C/Prop 32. |
| CRT layer frame + Engine Lemma (F₄ co-point rigidity) | **group_CRT_class** | needs 3-part `Z₃²` and an **elementary-abelian** 2-part. |
| Layer dictionary `d₃(W)` | **group_CRT_class** | pure `F₂[Z₃²]` arithmetic; reusable for any `Z₃²` 3-part. |
| Difference-set / overlap small-cycle obstructions (Thm A) | **polynomial_specific** | recipe re-runs; values do not. |
| Theorem A + witness `z*` (`d(base)=6`) | **polynomial_specific** | value is monomial-pinned. |
| Light-stabilizer classification (Prop 10) | **polynomial_specific** | hardest object; **false** off-monomials (see `Z₆×Z₁₄`). |
| Safe-sector reduction (homotopy R witness) | **polynomial_specific** *(corrected — see §4)* | sector-split is cover-class; the homotopy witness is monomial-tuned. |
| Smith-orbit + confined frame | **polynomial_specific** | numeric data bespoke; transport skeleton generic. |
| Slot-frame toolkit + weight-orbit walks | **polynomial_specific** | the AG(2,F₄) sub-toolkit is group_CRT; the floor lands at 6 only for this `A,B`. |
| ρ-link kill (Prop 31→32) | **polynomial_specific** | the 118-achiever list + ρ-links are this code's Smith-normal-form data. |

---

## 3. The doubling template

The reusable abstraction the proof instantiates. When **all four** conditions hold,
the template proves `d(cover) = 2·d(base)`:

1. **Free Z₂ cover.** The cover is the free Z₂ cover of the base (automatic for
   `Z_{2ℓ} → Z_ℓ` with deck `σ = ·x^ℓ`), with the *same* polynomials (so
   `π(Ã)=A`, `π(B̃)=B`).
2. **Homotopy R.** `σ_* = id` on `H₁(cover)`. This confines safe projections to
   `im Δ` via the chain-level identity `τ∘p = 1 + σ` ⟹ (with R) `τ_*∘p_* = 0`, i.e.
   `im p_* ⊆ ker τ_* = im Δ`.
3. **Both floors ≥ 2d.** The safe floor (the classes in `im p_*`, via the base's
   heavy Smith classes) and the dangerous floor (the classes in `ker p_*`, via the
   cover's diagonal lifts) both sit at `≥ 2·d(base)`.
4. **Tight diagonal lift.** A minimum-weight base logical `u*` lies *outside*
   `im Δ`, so `τ(u*) = (u*, u*)` is a genuine cover logical of weight `2·d(base)`,
   attaining the floor.

Two structural features observed in **both** known instances (gross and the new
pair, §5), likely additional template conditions worth proving in general:

- **`k` is preserved** under the doubling (12→12 for gross; 4→4 for the new pair).
  Not automatic — it constrains how `A,B` interact with the doubled direction.
- **`im Δ` and `ker p_*` are each exactly half of `k`**, and in fact
  `im τ_* = ker p_*` (dangerous sector = image of the transfer).

**Caution — doubling is not automatic.** The plain toric code is the cautionary
example: doubling x leaves the y-loop as the bottleneck, so `min(2L, L) = L` and the
distance does not move. The polynomials must mix the two directions enough that the
minimal logicals genuinely use the doubled direction (conditions 3–4 fail for toric).

---

## 4. Corrections to the first-pass analysis

Two places where an earlier, coarser pass was wrong or imprecise:

**(a) The engine's group obstacle.** Earlier phrasing — *"the square-zero radical
structure dies the moment the 2-part exceeds Z₂"* — is **wrong**: the gross engine is
literally built on `F₂[Z₂²]`. The correct statement: the CRT/Engine substrate needs
the **2-part elementary-abelian** (`Z₂ᵏ`, any `k` — it dies only when a `Z₄` or higher
factor appears, since then `(1+s)² ≠ 0`) **and** the **3-part exactly `Z₃²`** (the
co-point dichotomy "one zero + three distinct nonzero values" is literally
`|F₄ˣ| = 3`). The `Z₄` that appears in the gross *cover* (`Z₁₂×Z₆ ≅ Z₄×Z₂×Z₃²`)
never touches the engine, because the cover analysis is pushed down to the base via
`p`, `τ`.

**(b) The hypothesis for *doubling* vs *floor*.** The earlier "single hypothesis pair"
— *free Z₂ cover + `d(base)=μ_Z(base)`* — is only the **Theorem-B floor** condition;
it buys `d(cover) ≥ min{d, μ_Z} = d(base)`, **not** the doubling. The correct
hypothesis for `d(cover) = 2·d(base)` is the **four conditions of §3** (notably the
`im p_* ⊆ im Δ` confinement, which the floor condition does not give).

---

## 5. Verified second instance — `[[36,4,4]] → [[72,4,8]]`

A doubling pair **outside the gross/tour-de-gross lineage**, with a *different base
group*, on which the same safe/dangerous argument carries the distance.

- **Base** `[[36,4,4]]` on `G = Z₃×Z₆` (x order 3, y order 6):
  `A = x² + y + y³`, `B = 1 + x + y²`.
- **Cover** `[[72,4,8]]` on `Z₆×Z₆`, *same polynomials* — the free Z₂ double cover
  doubling x (`Z₆ → Z₃` mod 3, deck `σ = ·x³`).

Group frame: `Z₃×Z₆ ≅ Z₂ × Z₃²` — **3-part `Z₃²`** (F₄ rigidity survives) and
**2-part `Z₂`** (elementary-abelian, square-zero survives). So this base sits *inside*
the tractable engine frame of §4(a), unlike `Z₆×Z₁₄` (odd part `Z₃×Z₇`).

### Independent verification (32/32 checks)

Reproducible via
[`experiments/bb_lab/scripts/verify_doubling_pair_z3z6.py`](../experiments/bb_lab/scripts/verify_doubling_pair_z3z6.py)
(`uv run python scripts/verify_doubling_pair_z3z6.py` from `experiments/bb_lab`).
Codes built from `bb_lab` primitives; exact distances from the SAT solver (which
sidesteps the cover's 2³⁴-coset enumeration); the `p`/`τ`/`σ` maps validated as
genuine chain maps before any induced-map check.

| Claim | Result |
|---|---|
| base `(n,k)=(36,4)`, cover `(72,4)`; `dim H₁ = 4` both | ✓ |
| **base `d = 4`** (SAT: UNSAT ≤3, SAT 4) | ✓ |
| **cover `d = 8`** (SAT: **UNSAT ≤7**, SAT 8) | ✓ |
| `p`, `τ` are chain maps for `∂₁` and `∂₂`; `σ` commutes; `p∘τ=0`; `τ∘p=1+σ` | ✓ |
| `rank p_* = 2` ⟹ dangerous sector dim 2 | ✓ |
| `rank τ_* = 2` ⟹ `dim ker τ_* = 2 = dim im Δ` | ✓ |
| homotopy **R**: `σ_* = id` on `H₁(cover)` | ✓ |
| **linchpin** `im p_* ⊆ ker τ_* (= im Δ)` | ✓ |
| safe floor: the 3 classes in `im p_*` have **base** coset-min weight 8, 8, 8 (vs base `d=4`) | ✓ |
| upper bound: explicit weight-4 base logical `u*`, `[u*] ∉ ker τ_*`, `τ(u*)` is a nontrivial **dangerous** cover logical of weight 8 | ✓ |

Notes on rigor:

- The **linchpin is forced by R, not incidental**: the chain-level identity
  `τ∘p = 1+σ` (verified) plus `σ_* = id` (R, verified) gives `τ_*∘p_* = 0` over F₂,
  i.e. `im p_* ⊆ ker τ_*`. Same mechanism as gross.
- The **dangerous floor ≥ 8** is established via the **global** cover SAT result
  (`d=8` ⟹ *no* nonzero class, dangerous or safe, is below 8) rather than per-class
  enumeration (the dangerous cosets live in a 2³⁴ space). That global bound is
  *stronger* than the per-sector claim; the dangerous sector *achieves* 8 via `τ(u*)`.
- `d_Z(cover) = 8` is taken via the duality lemma + the weight-8 `τ(u*)` witness
  (only the X-side UNSAT was run directly). This is the proof's own route (Lemma 1).
- This instance validates the **logical template and the value** via solver-backed
  floors — it does **not** exercise the polynomial-specific *analytic* engine
  (Prop 10 / Prop 32). The user replaced the dangerous-floor classification with a
  direct minimization, which is stronger for one small code but does not scale to a
  family (gross's dangerous sector has `dim 6` → 63 classes over dimension-~70 cosets,
  which is the search the analytic route exists to avoid).

---

## 6. The base-floor halves, empirically: engine vs. difference-set

Theorem A (the base floor `d(base) ≥ 6`) is **two independent arguments** with
very different reach. Both were mapped against SAT ground truth (scripts:
[`engine_frame_sweep.py`](../experiments/bb_lab/scripts/engine_frame_sweep.py),
[`twosided_diffset_adapt.py`](../experiments/bb_lab/scripts/twosided_diffset_adapt.py),
[`twosided_floor_counterexample.py`](../experiments/bb_lab/scripts/twosided_floor_counterexample.py),
[`frobenius_obstruction_verify.py`](../experiments/bb_lab/scripts/frobenius_obstruction_verify.py)).

**One-sided half (CRT/F₄ engine) — `Ann(A), Ann(B) ≥ 6`.** *Frame-locked.* The
engine is *defined* only on `G ≅ Z₂²×Z₃²` (four `F₄` components + four `Z₂²`
slots); among catalogued BB codes only the gross base lives there. Even on the
frame: of weight-3 polynomials with a nonzero annihilator ~91% have `μ(Ann)≥6`
but ~9% fall below, and the coarse component profile does **not** predict which
(gross `A` and `1+y+y²` share a profile but have `μ=6` vs `4`). And the engine
half *alone never determines a distance* — over gross-shape `k>0` codes a
two-sided logical is strictly lighter than the one-sided floor ~47% of the time
(engine blind), and in the other ~53% it locates but cannot *prove* the floor
without the two-sided half.

**Two-sided half (difference-set combinatorics) — no light `(u_L,u_R)` cycle.**
*Frame-agnostic* (uses no `F₄`/CRT structure). It distills to checkable
predicates on `(A,B)`: **D1** `ov≤1` (Sidon difference sets); **D2** `dA∩dB=∅`;
**D3** coordinate separation.

- *The natural conjecture `D1 ∧ D2 ⟹ floor ≥ 2w` is **false**.* The obstruction is
  the characteristic-2 **Frobenius square**: `(1+x+y)² = 1+x²+y²`, so `A=B²` gives
  a two-sided cycle `(1,B)` of weight `1+w < 2w` while `A,B` are Sidon (`D1`) with
  `dA=2dB` disjoint from `dB` (`D2`). It is frame-independent and a *genuine
  distance obstruction* — on `Z₇²` it is a weight-4 **logical** in a `[[98,12,4]]`
  code (`μ_Z` drops to 4 everywhere). The earlier "`D1∧D2` suffices, `D3`
  dispensable" reading was wrong: an artifact of testing only gross-shape
  polynomials, which exclude the square shape `A=B²`.
- *Corrected criterion.* `D3` is exactly what excludes Frobenius (`A=B²` has
  `0 ∈ x(dA)∩x(dB)`; gross does not). SAT-checked over **general** weight-3
  polynomials: **`D1 ∧ D2 ∧ D3 ⟹ two-sided cycle floor ≥ 2w`, 0 violations / 4,144
  codes** (4001 on `Z₇²`, 144 on `Z₆²`).
- *Proof status.* Unconditional under `D1∧D2`: parity; `(1,1)` impossible;
  `(1,t) ⟹ t≥w` (each `B`-translate contributes ≤1 cell to an `A`-translate). The
  gap is the minimal `(1,w)` cycle, where Frobenius lives. With the full
  **spike–spread** structure (which implies `D3`) the gross argument generalizes
  and *proves* the `2w` floor, modulo recomputing the projections' 1-variable
  annihilator weights per polynomial. Whether `D3` *alone* suffices is open
  (empirically yes for `w=3`).

The predicates and the Frobenius gate are packaged in
[`bb_lab.diffset_predicates`](../experiments/bb_lab/src/bb_lab/diffset_predicates.py)
(`is_sidon`, `difference_sets_disjoint`, `coordinate_separated`,
**`is_frobenius_related`**, `two_sided_hypothesis`).

**Net for the program.** The two-sided half is the **frame-portable** foundation
(it ports across `F₄/F₈/F₆₄`; the Frobenius obstruction is also frame-independent),
with correct lemma `D1∧D2∧D3 ⟹ 2w`. The one-sided (engine) half stays frame-locked.
A general base-floor theory should be built on the difference-set side, with the
Frobenius square as a named, mandatory exclusion.

---

## 7. Reusable core vs. per-code cost

**Genuinely reusable (prove once, instantiate freely):**
- chain substrate + PAR + X–Z duality (**generic_BB**); already parametric in Lean;
- the *entire* free-Z₂ cover skeleton — `p`, `τ`, block boundary, slice identity,
  Theorem B/D assembly shells (**cover_class**) — parameterized by
  `(d(base), μ_Z(base))`. **On their own these deliver only `min{d, μ_Z}`, never the
  doubled value.**

**Per-code, mechanical:** re-instantiate `∂₁,∂₂`; check `A,B` odd-weight; for a
same-frame code recompute the multiplier table and `W`-reads; verify the R squaring
identity and the no-double-wrap x-advance bound.

**Per-code, needs new ideas:** Theorem A (the base floor — can *fail*, e.g. a `Z₃×Z₅`
frame has a weight-4 cycle **[reported, not re-verified here]**); Prop 10
(light-stabilizer classification); Prop 32 (slot-frame walk + ρ-link kill); a fresh
tight witness.

**The single biggest obstacle to a family theorem:** the engine's `F₄` co-point
rigidity is a `Z₃²`-only phenomenon and the square-zero radical needs an
elementary-abelian 2-part. The one genuinely-new corpus base, `Z₆×Z₁₄ [[168,12,6]]`,
has odd part `Z₃×Z₇` → heterogeneous `F₈/F₆₄` layers where this rigidity fails; SAT
confirms its covers double **[reported, not re-verified here]** but no analytic
Prop-10/Prop-32 analogue is known there — an open problem.

---

## 8. Bottom line

- **Factor the cover machinery as a parametric Lean layer.** Substrate + duality +
  the free-Z₂ cover skeleton are reusable, low-risk infrastructure for the whole
  doubling program, taking `(d(base), μ_Z(base))` as inputs.
- **Build the base-floor theory on the difference-set (two-sided) side** (§6): it
  is frame-agnostic, distills to `D1 ∧ D2 ∧ D3`, and `is_frobenius_related` must be
  a mandatory exclusion gate. The CRT/F₄ engine (one-sided) half is frame-locked and
  is only one of two halves — never sufficient alone.
- **State the doubling hypothesis as the four conditions of §3**, not the coarser
  floor condition. The cover supplies the factor-2; the base floor supplies the only
  number; conditions 2–4 are what upgrade `≥ d` to `= 2d`.
- **The mechanism is multi-instance.** The `[[36,4,4]] → [[72,4,8]]` pair (§5) is a
  verified doubling outside the gross lineage, in the same `Z₃²`/elementary-2-part
  engine frame — a positive signal that the family route is broader than the single
  tour-de-gross row.
- **Claim the mechanism and the family route, not the solver-known values.** The
  cover dichotomy is family-portable; `d = 2·d(base)` is carried by polynomial-specific
  engines that currently live only over `Z₃²/F₄`.

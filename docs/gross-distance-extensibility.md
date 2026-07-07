# Anatomy and extensibility of the d(gross)=12 proof

Companion to [`gross-distance-proof.md`](gross-distance-proof.md). It maps the
distinct parts of that proof and records, for each, how tightly the argument is
welded to the specific code versus how far it transfers to other bivariate-bicycle
(BB) codes. It also records the **doubling template** the proof instantiates, two
corrections to an earlier (coarser) pass at this analysis, and an independently
**verified second doubling pair** outside the gross lineage (it confirms the cover
scaffolding and the doubled *value* by SAT, but does not exercise the analytic floor
engine — see §5).

Scope note: the structural / proof-theoretic content here is grounded in the proof
text and (for the new pair) in a 32/32-check computation. A handful of *quantitative
corpus* claims (the 16,867-code cover sweep; the `Z₆×Z₁₄` weight-8 count; the
two-gross self-test) come from the `bb_lab` cover-cascade tooling and the analysis
agents and are flagged inline as **[reported, not re-verified here]**. An adversarial
re-verification (2026-06-29) independently reproduced the §1/§3/§4/§5/§6 computations
against `bb_lab` and corrected two corpus claims — the §6 engine-frame exclusivity and
the §6 `D1∧D2∧D3` count (both below).

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
| Safe-sector reduction (homotopy R witness) | **cover_class** *(upgraded by A12 — see §3 update)* | sector-split is cover-class; the homotopy witness is now generic: (R) ⟺ `k` preserved ⟺ Bezout membership, with `deckTrivial_of_bezout` producing the certificate from any witness pair. |
| Smith-orbit + confined frame | **polynomial_specific** | numeric data bespoke; transport skeleton generic. |
| Slot-frame toolkit + weight-orbit walks | **polynomial_specific** | the AG(2,F₄) sub-toolkit is group_CRT; the floor lands at 6 only for this `A,B`. |
| ρ-link kill (Prop 31→32) | **polynomial_specific** | the 118-achiever list + ρ-links are this code's Smith-normal-form data. |

---

## 3. The doubling template

The reusable abstraction the proof instantiates. It is a **conditional reduction**,
not a self-contained theorem: when conditions 1–4 hold they bring `d(cover) = 2·d(base)`
down to the two floor inputs of condition 3 — which the template does **not** itself
prove (those floors are discharged per-instance: by the analytic engine for gross, by a
global SAT call in §5). The conditions are also **layered, not independent** — condition
2 is the mechanism that establishes the safe half of condition 3, and condition 4
supplies the matching tight upper bound. With those caveats, conditions 1–4 assemble to
`d(cover) = 2·d(base)`:

1. **Free Z₂ cover.** The cover is the free Z₂ cover of the base (automatic for
   `Z_{2ℓ} → Z_ℓ` with deck `σ = ·x^ℓ`), with the *same* polynomials (so
   `π(Ã)=A`, `π(B̃)=B`).
2. **Homotopy R.** `σ_* = id` on `H₁(cover)`. This confines safe projections to
   `im Δ` via the chain-level identity `τ∘p = 1 + σ` ⟹ (with R) `τ_*∘p_* = 0`, i.e.
   `im p_* ⊆ ker τ_* = im Δ`.
3. **Both floors ≥ 2d.** The safe floor (the classes in `im p_*`, via the base's
   heavy Smith classes / Prop 32) and the dangerous floor (the classes in `ker p_*`,
   via the light-stabilizer classification Prop 10 + the slice identity
   `|b|+2·m(b) ≥ 2d`) both sit at `≥ 2·d(base)`. (The diagonal lift `τ(u*)` is *not*
   the dangerous-floor mechanism — it is the condition-4 tightness witness, below.)
4. **Tight diagonal lift.** A minimum-weight base logical `u*` lies *outside*
   `im Δ`, so `τ(u*) = (u*, u*)` is a genuine cover logical of weight `2·d(base)`,
   attaining the floor.

> **Update (2026-07-02, A12 — condition 2 is solved).** Theorem
> (`experiments/bb_lab/notes/A12_deck_homotopy_R.md` §3): for every free Z₂ BB
> cover, the following are **equivalent**: (R); `k(cover) = k(base)`;
> `1+x^ℓ ∈ (A,B)` (Bezout membership in `F₂[G̃]`). In particular (R) is **not
> automatic** — explicit weight-3 counterexamples exist (e.g. `Z₆×Z₃` cover
> with `A = 1+y+y²`, `B = 1+x²+x⁴`: `k` jumps 8→16 and `σ_* ≠ id` on a
> 16-dimensional `H₁`; even the strict IBM monomial shape admits failures) —
> but it is **free exactly on the k-preserving class**, which the A9 screen
> already computes, and every historically checked cover (gross both
> directions, the §5 pair, Z₆×Z₁₄ both directions, all 152 A9 doubles:
> 157/157) is in that class. The membership direction is constructive: a
> Bezout witness `P⋆A + Q⋆B = 1+x^ℓ` yields the homotopy certificate with
> module maps (`deckTrivial_of_bezout` in `BBDoubling.lean`); both instance
> identities — gross's `(1+x²)B² = 1+x⁶` and the pair's `p·B = 1+x³` — are
> its `P = 0` case. Two further A12 facts: the `Δ`-linchpin `im p_* ⊆ im Δ`
> is *equivalent* to (R) (Δ is the transfer-LES connecting map), and the
> F₂-additive certificate form of `deckTrivial_of_homotopy_certificate` is
> *complete* — semantic (R) is equivalent to solvability of
> `1+σ = ∂₂∘C + E∘∂₁` (split `C₁ = ker ∂₁ ⊕ W`; define `C` on cycles by (R),
> absorb `W` into `E`) — so the certificate route loses nothing. Still open
> (A12 §4): the quantitative refinement `dim (1+σ)H₁ = k(cover) − k(base)`
> (equivalently, vanishing of the deck-Bockstein composite `δ₁∘δ₂`), exact in
> every instance and block swept so far.

Two structural features observed in **both** known instances (gross and the new
pair, §5):

- **`k` is preserved** under the doubling (12→12 for gross; 4→4 for the new
  pair). Not automatic — and by the A12 theorem above this is not an
  independent condition: it is *equivalent* to condition 2 (R).
- **`im Δ` and `ker p_*` are each exactly half of `k`**, and in fact
  `im τ_* = ker p_*` (dangerous sector = image of the transfer).

> **Update (2026-07-04, A14 — the "observed" features are theorems, and the
> safe sector is canonical).** Under (R), Prop A14.1
> (`experiments/bb_lab/notes/A14_safe_floor_criterion_plan.md` §2) proves:
> `p₂ = 0` on H₂ and the connecting map `Δ = δ₂` is **injective** (via the
> Bezout membership `ε ∈ (A,B)`); `im p_* = im Δ` **exactly**, of dimension
> `k/2 = dim R/(A,B)` (so `rank p_* = 2` resp. `6` above are forced, and
> `im τ_* = ker p_*` is LES exactness, hypothesis-free); the safe classes are
> canonically `Δ(ann_R(A,B) \ 0)` with the explicit **seam-carry
> representatives** `seamC(ζ)` = the x-wrap masks of `(Ãζ̃, B̃ζ̃)` (=
> `BBCover.seamC`, matched bit-for-bit against `SeamTables.lean`); and coset
> minima are **constant on G-translation orbits** — gross's 63 Smith classes
> collapse to 13 y-orbits (the MIm transport count) and further to **5**
> full-G orbits. Also automatic at `k̃ = k`: the deck-Bockstein composite
> `δ₁∘δ₂ = 0` (the A12 §4 remainder has content only off the doubling
> regime). Verified numerically on gross, pair72, and a CE2 negative control
> (`a14_seam_formula_check.py`, 30/30).

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

## 5. Verified second doubling pair — `[[36,4,4]] → [[72,4,8]]`

A doubling pair **outside the gross/tour-de-gross lineage**, with a *different base
group*, on which the cover scaffolding reproduces and the doubled distance is confirmed
by SAT — the analytic safe/dangerous *engine* (Prop 10 / Prop 32) is **not** re-run here
(see the rigor notes below).

> **Lean status (2026-07-02).** This pair is now **proven in Lean at the chain and
> Pauli levels**, end-to-end through the parametric doubling layer
> (`QEC/Stabilizer/Framework/Homological/{BBCover,BBDoubling}.lean`):
> `pair72_chain_distance_eq_8` / `pair72_pauli_distance_eq_8`
> (`QEC/Stabilizer/Codes/BivariateBicycle/Z3Z6/`), axiom bar identical to gross
> (standard three + `native_decide`).  All four template conditions of §3 are
> discharged: the base floor by weight-≤3 kernel sweeps, (R) by the single
> polynomial identity `p·B = 1+x³` (weight-8 `p`; simpler than gross's
> `(1+x²)B² = 1+x⁶`) through the layer's chain-homotopy certificate, the dangerous
> floor by the layer's generic single-shape rung over the 24-class light-boundary
> census, and the safe floor by three per-Smith-class `2¹⁸` sweeps (`dim ker ∂₂ = 2`
> here vs gross's 6, so no CRT engine is needed — the sweeps ARE the floor).  The
> `StabilizerCodeWithDistance 72 4 8` packaging is also done (S3.9):
> `pair72StabilizerCodeWithDistance` in `Z3Z6/StabilizerCode.lean`, mirroring the
> gross Phase-5 packaging.  Data provenance:
> `experiments/bb_lab/scripts/gen_pair72_z6z6_data.py` (instance data) and
> `gen_pair72_packaging_data.py` (packaging data, 15-check ALL-PASS gate).

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
slots); among the **named/literature (Bravyi Table I)** BB codes only the gross base
lives there — but the generated corpus has **812 `k>0` codes on this frame** (including
non-gross `[[72,12,6]]`-shape codes), so the frame is *not* gross-exclusive **[corpus
figure from private-side `bb_instances.duckdb`; not re-runnable in this worktree]**.
**A9 correction (2026-07-02):** the frame is not even *anchorability*-exclusive — the
presentation-orbit census over the corpus's `d ≥ 6` codes finds **six anchorable
`[[72,12,6]]` codes: gross plus FIVE genuinely new ones** (inequivalent under the full
captured equivalence; a raw check on stored canonical forms sees 0/812 because the
mirrored-projection gate is not Aut-invariant), and **three of the five have exact
`[[144,12,12]]` y-covers** — engine-frame gross twins.  See
`experiments/bb_lab/notes/A9_lean_target_screen.md` §T2. Even
on the
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
- *Apparent corrected criterion (frame-limited).* On `Z₆²`/`Z₇²`, `D3` excludes
  Frobenius (`A=B²` has `0 ∈ x(dA)∩x(dB)` there; gross does not), and
  **`D1 ∧ D2 ∧ D3 ⟹ two-sided cycle floor ≥ 2w`** is SAT-verified with 0 violations
  among **4,144 SAT-checked pairs** (`Z₇²`: 4000 of an 8496-pair population, the sweep
  capping at 4000; `Z₆²`: all 144; also holds on `Z₉×Z₆`, `Z₁₂×Z₆`) — a clean but
  partial sample (`Z₇²` under half), not an exhaustive check.
- ***…but `D1∧D2∧D3` itself fails on wider frames.*** `D3`'s exclusion of Frobenius
  is a small-modulus coincidence. On **`Z₈²`, `Z₁₃²`, `Z₁₅²`** there exist Frobenius
  squares `A=B²` with `D1∧D2∧D3` *all true* — a "spread" `B` whose doubled difference
  set stays coordinate-disjoint (e.g. `Z₈²`: `B={(0,0),(1,1),(4,5)}`,
  `A=B²={(0,0),(0,2),(2,2)}`, SAT two-sided floor `4 < 6`). So the corrected
  conjecture is **also not frame-agnostic**. The robust exclusion is the *explicit
  algebraic gate* `is_frobenius_related`, not `D3`: the conjectured criterion is
  **`D1∧D2∧D3 ∧ ¬is_frobenius_related`** (`robust_floor_hypothesis`) — *necessary*
  (Frobenius squares are genuine obstructions that `D3` misses), with 0 violations in
  a 200-sample `¬Frobenius` `Z₈²` check, but **sufficiency is open** (higher Frobenius
  powers `A=B⁴`, shared-factor obstructions untested).
- *Proof status (the conjecture is NOT proven in general).* The gross proof is an
  **instance proof**, not a parametric theorem: only `(1,1)` is parametric (pure
  `D2`); the `(1,3)`/`(2,2)` cases hard-code per-polynomial facts (triangle
  chiralities, the 1-variable fact "`Ann(1+x+x²)` has min weight 4", the multiset
  `{3,1}≠{2,1,1}`). Unconditional under `D1∧D2`: parity; `(1,1)` impossible;
  `(1,t) ⟹ t≥w` (each `B`-translate contributes ≤1 cell to an `A`-translate). The
  gap is the minimal `(1,w)` cycle, where Frobenius lives.
- *The spike–spread "generalization" is a RECIPE, and it is incomplete.* Re-running
  the gross case analysis on another spike–spread `(A,B)` requires discharging the
  per-polynomial obligations, which **can fail**: the `(2,2)` step needs the spread's
  1-variable annihilator min-weight `> 2`, and that fails for ≈8–10% of spike–spread
  `D1∧D2` codes on larger frames (30/400 on `Z₉×Z₆`, 39/400 on `Z₆×Z₁₂`; 0/100 on
  `Z₆²`) — *even though the floor still equals `2w` there* (SAT-confirmed). So the gross
  technique is frame-fragile: a complete prover on `Z₆²`, a leaky recipe beyond it.
- *Empirical robustness of the floor itself.* `D1∧D2∧spike-spread ⟹ floor = 2w` holds
  with 0 violations over 900 codes (`Z₆²`, `Z₉×Z₆`, `Z₆×Z₁₂`), the floor being *exactly*
  `2w` in every case. So the target is a robust conjecture; the gross proof supplies one
  instance + a partial (automatable) recipe. Closing the ~10% the recipe drops — and
  whether `D3` *alone* suffices (empirically yes, `w=3`) — is the open Layer-2 work.

The predicates and the Frobenius gate are packaged in
[`bb_lab.diffset_predicates`](../experiments/bb_lab/src/bb_lab/diffset_predicates.py)
(`is_sidon`, `difference_sets_disjoint`, `coordinate_separated`,
**`is_frobenius_related`**, `two_sided_hypothesis`).

**Net for the program.** The two-sided half is *more* frame-portable than the
engine, but it is **not capturable by clean difference-set predicates alone**. The
sequence `D1∧D2` → `D1∧D2∧D3` each looked sufficient on its test frames and each
broke when the frame widened (gross-shape → all weight-3; then `Z₆²/Z₇²` → `Z₈²/Z₁₃²/Z₁₅²`).
The stable object is the **explicit algebraic obstruction** (`is_frobenius_related`),
not a Sidon-style condition. So a real base-floor theory must *enumerate and exclude
algebraic obstructions explicitly* (Frobenius squares first; then higher powers /
shared factors) and prove a floor on the complement — `D1∧D2∧D3` is a useful but
frame-fragile filter, the one-sided (engine) half stays frame-locked, and sufficiency
of `D1∧D2∧D3 ∧ ¬Frobenius` is itself open.

> **Update (2026-07-07, A15 Entries 8–11 — the class small-cycle theorem
> closes this arc for the mirrored class).** The base-floor theory this
> section called for now exists as an **unconditional theorem** on the
> (iii)-mirrored class (write-up of record:
> `experiments/bb_lab/notes/A16_class_theorem_writeup.md`; certifier
> `experiments/bb_lab/scripts/a15_class_certify.py`): for weight-3
> instances with D1 ∧ D2 ∧ (iii) ∧ Ann ≠ 0 on a floor-bearing frame,
> **no nonzero 1-cycle of weight ≤ 5 exists**. Three findings
> revise this section's conclusions *for class members*:
> (1) the one-sided engine half is **not** frame-locked to `Z₃²` — the
> support dichotomy is field-generic (only value-rigidity is F₄-bound),
> so the `Z₂²`-frame floor runs over any odd part (first new instance:
> `Z₆×Z₁₄ [[168,12,6]]`, certified, odd part `Z₃×Z₇`);
> (2) the Frobenius obstruction is subsumed: the weight-3 triangle image
> is *identically* `B² + c` (char-2 identity), and `(iii) ∧ D1` exclude
> `dA = 2·dB` outright — including the `Z₈²`-spread variants that broke
> `D3` — so on the class no explicit `is_frobenius_related` gate is
> needed;
> (3) the `(2,2)` obligation's stable invariant is the **difference
> multiset**, not coordinate profiles: the kill is exact multiset
> accounting (atoms → translate-rigidity → a D2 funnel), and its only
> live exceptional families are 5-torsion-confined, dying against
> `Ann ≠ 0` (no vanishing weight-3 sums of 5th roots in char 2).
> Off-class (non-mirrored pairs), this section's caution stands
> unchanged — the falsifier families live exactly there.

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

**A9 update (2026-07-02): an in-frame engine target now exists.** The obstacle above
concerned leaving the frame; the A9 census (§6) shows the engine's own frame carries
**three new `[[72,12,6]] → [[144,12,12]]` doubling pairs beyond gross** (hit3:
`A = y³+x+x², B = y+xy²+x²`, and two siblings — all sharing gross's `A` up to
normalization). Their bases have 36 cells, so the direct-sweep route used for the §5
pair (`2¹⁸` cosets) is out of reach (`2³⁶`): a full `d = 12` proof for any of them
requires re-instantiating the polynomial-specific engine tables (Prop-10
classification, MIm dispatch and floor leaves) — i.e. these are the natural targets
where the CRT/F₄ engine is *necessary*, not decorative, and where its parametrization
would pay off.

**A14 update (2026-07-04): the three targets' safe floors are SAT-certified, and a
necessary-screen battery now front-runs the hunts.** Fork A14 (OQ4;
`experiments/bb_lab/notes/A14_safe_floor_criterion_plan.md`) built a cost-ordered
battery of *necessary* screens for condition 3's safe half — S0 raw seam weights
(free) → S1/S1+ boundary descent → S2 CRT-block kills → S4 per-orbit-rep coset SAT —
each rejection carrying an explicit light-coset-element certificate. On the 638-row
T1 corpus (exact ground truth recomputed for every row): 86% of SF-failures rejected
by the cheap tiers at zero false rejections, and **every k-preserving short is
SF-false** — on the direct-sweep frames the safe floor alone separates doubles from
shorts. On the engine frame, Prop A14.1's full-G transport (63 classes → **5** orbit
reps) makes S4 decisive in seconds: **hit3/4/6-y all have `SeamCosetFloor 12`
SAT-certified (~25 s each, floors exactly tight at 12 — the gross pattern), none is
overlap-rescued**, so all three are viable engine targets; gross's Lean-proven floor
is independently SAT-cross-checked in 24 s; and the `[[288,12,18]]` anti-instance
fails the safe floor on **both** axes with certificates (x: raw seam weight 24; y:
SAT witness weight 34). The engine re-instantiation itself (Prop-10 + MIm tables for
the new `(A,B)`) remains the open per-code work — the battery only settles *which*
codes deserve it.

---

## 8. Bottom line

- **Factor the cover machinery as a parametric Lean layer.** ✅ **Done (2026-07-02)**:
  `Framework/Homological/BBCover.lean` (the `XDoubleCoverData` bundle — five data
  fields, four finite obligations — with the full transfer/sheet/seam apparatus
  derived generically) and `BBDoubling.lean` (the template of §3 as theorems:
  `chainWeight_ge_of_strongBaseFloor` for the Theorem-B floor,
  `deckTrivial_of_homotopy_certificate` for (R), generic single-/pair-shape dangerous
  rungs, `safeFloor_of_seamCosetFloor`, and the assemblies
  `chain_distance_eq_double` / `pauli_distance_eq_double`).  The gross retrofit onto
  the layer is deliberately deferred (its `native_decide` leaves embed the seam
  definitions definitionally).
- **Build the base-floor theory on the difference-set (two-sided) side** (§6): it
  is frame-agnostic, distills to `D1 ∧ D2 ∧ D3`, and `is_frobenius_related` must be
  a mandatory exclusion gate. The CRT/F₄ engine (one-sided) half is frame-locked and
  is only one of two halves — never sufficient alone.
- **State the doubling result as the conditional reduction of §3**, not a
  self-contained theorem: the four conditions bring `= 2d` down to condition 3's two
  floor inputs but do not prove them (still discharged per-instance — analytically for
  gross, by kernel sweeps for the §5 pair in Lean, by SAT elsewhere). The cover
  supplies the factor-2; the base floor supplies the only number; conditions 2–4
  (layered, not independent) upgrade `≥ d` to `= 2d` *given* the floors.
- **The mechanism is multi-instance — now in Lean, not just in SAT.** The
  `[[36,4,4]] → [[72,4,8]]` pair (§5) is proven through the parametric layer at the
  chain and Pauli levels with the gross axiom bar; and the A9 census (§6) shows the
  engine frame itself carries three further `[[144,12,12]]` doubling pairs beyond
  gross (§7) — the family route is broader than the single tour-de-gross row in both
  directions.
- **Claim the mechanism and the family route, not the solver-known values.** The
  cover dichotomy is family-portable (and now a reusable Lean layer);
  `d = 2·d(base)` is carried by per-instance floors — polynomial-specific engines
  over `Z₃²/F₄` at gross scale, direct kernel sweeps at `2¹⁸` scale.
